import OAI.Geometry.IsometricImmersion.Metrics.ActualLowMetricFloor
import OAI.Geometry.IsometricImmersion.Metrics.MetricPatchOpen

namespace OAI

noncomputable section
open Set Filter Function
open scoped ContDiff Topology Matrix Matrix.Norms.Elementwise

namespace SmoothLocal.Pulse
open SmoothLocal.Geometry SmoothLocal.Perturbation

theorem metricQuadraticValue_sub_bound {A B : MetricMatrix} {v : Coord} {epsilon : ℝ}
    (he : 0 ≤ epsilon) (hv : ‖v‖ ≤ 1)
    (hAB : ∀ i j, |A i j-B i j| ≤ epsilon) :
    |metricQuadraticValue A v-metricQuadraticValue B v| ≤ 4*epsilon := by
  have hvB (i : Fin 2) : |v i| ≤ 1 := (norm_le_pi_norm v i).trans hv
  have hterm (i j : Fin 2) : |v i*(A i j-B i j)*v j| ≤ epsilon := by
    rw [abs_mul,abs_mul]
    have hleft : |v i| * |A i j-B i j| ≤ epsilon :=
      (mul_le_mul (hvB i) (hAB i j) (abs_nonneg _) (by norm_num)).trans_eq (one_mul _)
    exact (mul_le_mul hleft (hvB j) (abs_nonneg _) he).trans_eq (mul_one _)
  have heq : metricQuadraticValue A v-metricQuadraticValue B v =
      (v 0*(A 0 0-B 0 0)*v 0+v 0*(A 0 1-B 0 1)*v 1)+
        (v 1*(A 1 0-B 1 0)*v 0+v 1*(A 1 1-B 1 1)*v 1) := by
    simp only [metricQuadraticValue,Matrix.mulVec,dotProduct,Fin.sum_univ_two]
    ring
  rw [heq]
  exact (abs_add_le _ _).trans ((add_le_add
    ((abs_add_le _ _).trans (add_le_add (hterm 0 0) (hterm 0 1)))
    ((abs_add_le _ _).trans (add_le_add (hterm 1 0) (hterm 1 1)))).trans_eq (by ring))

theorem exists_metric_positive_value_tolerance
    {gStar : MetricField} {V : Set Coord}
    (hgStar : SmoothPositiveOn gStar V) (hV : IsOpen V) (hSV : modelSquare ⊆ V) :
    ∃ epsilon : ℝ, 0 < epsilon ∧ ∀ p ∈ modelSquare, ∀ A : MetricMatrix,
      A.IsHermitian → (∀ i j, |A i j-gStar p i j| ≤ epsilon) → A.PosDef := by
  let T := modelSquare ×ˢ Metric.sphere (0 : Coord) 1
  have hT : IsCompact T := modelSquare_isCompact.prod (isCompact_sphere (0 : Coord) 1)
  have hcont : ContinuousOn (fun pv : Coord × Coord => metricQuadraticValue (gStar pv.1) pv.2) T := by
    intro pv hpv
    apply (metricQuadraticValue_continuousAt (fun i j =>
      (((hgStar.1 i j).contDiffAt (hV.mem_nhds (hSV hpv.1))).continuousAt.comp
        continuous_fst.continuousAt)) (fun i => by fun_prop)).continuousWithinAt
  have hpos (pv : Coord × Coord) (hpv : pv ∈ T) : 0 < metricQuadraticValue (gStar pv.1) pv.2 := by
    have hnorm : ‖pv.2‖ = 1 := by simpa only [Metric.mem_sphere,dist_zero_right] using hpv.2
    have hne : pv.2 ≠ 0 := by intro he; rw [he,norm_zero] at hnorm; norm_num at hnorm
    simpa only [metricQuadraticValue,star_trivial] using (hgStar.2 pv.1 (hSV hpv.1)).dotProduct_mulVec_pos hne
  obtain ⟨lambda,hlambda,hfloor⟩ := hT.exists_forall_le' hcont hpos
  refine ⟨lambda/8,by positivity,?_⟩
  intro p hp A hA hclose
  apply posDef_of_positive_on_sphere hA
  intro v hv
  have hnorm : ‖v‖ = 1 := by simpa only [Metric.mem_sphere,dist_zero_right] using hv
  have hdiff := metricQuadraticValue_sub_bound (by positivity : 0 ≤ lambda/8) hnorm.le hclose
  have hl := hfloor (p,v) ⟨hp,hv⟩
  linarith [(abs_le.mp hdiff).1]

theorem testMetric_coeff_contDiffOn {gStar : MetricField} {V : Set Coord}
    (hgStar : SmoothPositiveOn gStar V) (q0 a : ℝ) (N : ℕ) (delta tau : ℝ) (i j : Fin 2) :
    ContDiffOn ℝ ∞ (fun q => testMetric gStar q0 a N delta tau q i j) V := by
  have hp : ContDiff ℝ ∞ (fun q => pulseTensor q0 a N delta tau q i j) :=
    (contDiff_apply ℝ ℝ j).comp
      ((contDiff_apply ℝ (Fin 2 → ℝ) i).comp (pulseTensor_contDiff q0 a N delta tau))
  exact (hgStar.1 i j).add hp.contDiffOn

theorem testMetric_isHermitian {gStar : MetricField} {V : Set Coord}
    (hgStar : SmoothPositiveOn gStar V) (q0 a : ℝ) (N : ℕ) (delta tau : ℝ)
    {p : Coord} (hp : p ∈ V) : (testMetric gStar q0 a N delta tau p).IsHermitian := by
  have hT : (pulseTensor q0 a N delta tau p).IsHermitian := by
    change (pulseTensor q0 a N delta tau p)ᴴ=pulseTensor q0 a N delta tau p
    ext i j
    simpa only [Matrix.conjTranspose_apply,star_trivial] using pulseTensor_symmetric q0 a N delta tau p j i
  exact (hgStar.2 p hp).isHermitian.add hT

theorem testMetric_positive_on_modelSquare_eventually
    {gStar : MetricField} {V : Set Coord}
    (hgStar : SmoothPositiveOn gStar V) (hV : IsOpen V) (hSV : modelSquare ⊆ V)
    (q0 a : ℝ) (ha : 0 < a) (N : ℕ) (hN : 0 < N) (delta : ℝ) :
    ∀ᶠ tau : ℕ in atTop, ∀ p ∈ modelSquare,
      (testMetric gStar q0 a N delta (tau : ℝ) p).PosDef := by
  obtain ⟨epsilon,he,hpositive⟩ := exists_metric_positive_value_tolerance hgStar hV hSV
  filter_upwards [pulseTensor_finite_coeff_jets_eventually_small q0 a ha 0 N hN delta he]
    with tau hpulse
  intro p hp
  apply hpositive p hp _ (testMetric_isHermitian hgStar q0 a N delta (tau : ℝ) (hSV hp))
  intro i j
  have hh := hpulse.2 i j 0 le_rfl p
  simpa only [norm_iteratedFDeriv_zero,Real.norm_eq_abs,testMetric,Pi.add_apply,Matrix.add_apply,
    add_sub_cancel_left] using hh

end SmoothLocal.Pulse

end

end OAI
