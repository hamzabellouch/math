import OAI.Geometry.IsometricImmersion.Pulses.ActualQPulseForcing

namespace OAI

noncomputable section
open Set Filter
open scoped ContDiff Topology BigOperators Matrix Matrix.Norms.Elementwise

namespace SmoothLocal.Pulse
open SmoothLocal.Geometry SmoothLocal.HighEquation

def affineFirstJetMap (R : MetricMatrix) (a : CurvatureFirstInput) : CurvatureFirstInput :=
  ((fun i j => ∑ u, ∑ v, R u i*R v j*a.1 u v),
    (fun k i j => ∑ u, ∑ v, ∑ w, R u i*R v j*R w k*a.2 w u v))

theorem affineFirstJetMap_sub (R : MetricMatrix) (a b : CurvatureFirstInput) :
    affineFirstJetMap R (a-b) = affineFirstJetMap R a-affineFirstJetMap R b := by
  apply Prod.ext
  · funext i j
    simp only [affineFirstJetMap,Prod.fst_sub,Pi.sub_apply,Fin.sum_univ_two]
    ring
  · funext k i j
    simp only [affineFirstJetMap,Prod.snd_sub,Pi.sub_apply,Fin.sum_univ_two]
    ring

theorem actualCurvatureFirstInput_affinePullback {g : MetricField} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (b : Coord) (R : MetricMatrix)
    (p : Coord) (hp : affineCoordinates b R p ∈ U) :
    actualCurvatureFirstInput (affinePullbackMetric g b R) p =
      affineFirstJetMap R (actualCurvatureFirstInput g (affineCoordinates b R p)) := by
  apply Prod.ext
  · funext i j
    simp only [actualCurvatureFirstInput,affineFirstJetMap,affinePullbackMetric,
      Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_two]
    ring
  · funext k i j
    exact coordPartial_affinePullbackMetric hg hU b R p hp k i j

private theorem abs_sum_fin_two_le {f : Fin 2 → ℝ} {e : ℝ}
    (hf : ∀ i, |f i| ≤ e) : |∑ i, f i| ≤ 2*e := by
  simp only [Fin.sum_univ_two]
  exact ((abs_add_le _ _).trans (add_le_add (hf 0) (hf 1))).trans_eq (by ring)

theorem affineFirstJetMap_norm_le_eight (R : MetricMatrix)
    (hR : ∀ i j, |R i j| ≤ 1) (a : CurvatureFirstInput) {e : ℝ}
    (he : 0 ≤ e) (ha : ‖a‖ ≤ e) : ‖affineFirstJetMap R a‖ ≤ 8*e := by
  have hval (i j : Fin 2) : |a.1 i j| ≤ e := by
    simpa only [Real.norm_eq_abs] using
      (((norm_le_pi_norm (a.1 i) j).trans (norm_le_pi_norm a.1 i)).trans (norm_fst_le a)).trans ha
  have hder (k i j : Fin 2) : |a.2 k i j| ≤ e := by
    simpa only [Real.norm_eq_abs] using
      ((((norm_le_pi_norm (a.2 k i) j).trans (norm_le_pi_norm (a.2 k) i)).trans
        (norm_le_pi_norm a.2 k)).trans (norm_snd_le a)).trans ha
  have hR2 (i j u v : Fin 2) : |R u i*R v j| ≤ 1 := by
    rw [abs_mul]
    simpa only [one_mul] using mul_le_mul (hR u i) (hR v j) (abs_nonneg _) zero_le_one
  have hR3 (i j k u v w : Fin 2) : |R u i*R v j*R w k| ≤ 1 := by
    rw [abs_mul]
    simpa only [one_mul] using mul_le_mul (hR2 i j u v) (hR w k) (abs_nonneg _) zero_le_one
  have hv (i j u v : Fin 2) : |R u i*R v j*a.1 u v| ≤ e := by
    rw [abs_mul]
    simpa only [one_mul] using mul_le_mul (hR2 i j u v) (hval u v) (abs_nonneg _) zero_le_one
  have hd (k i j u v w : Fin 2) : |R u i*R v j*R w k*a.2 w u v| ≤ e := by
    rw [abs_mul]
    simpa only [one_mul] using mul_le_mul (hR3 i j k u v w) (hder w u v) (abs_nonneg _) zero_le_one
  have hvsum (i j : Fin 2) : |∑ u, ∑ v, R u i*R v j*a.1 u v| ≤ 4*e := by
    have hh := abs_sum_fin_two_le (fun u => abs_sum_fin_two_le (hv i j u))
    convert hh using 1
    ring
  have hdsum (k i j : Fin 2) : |∑ u, ∑ v, ∑ w, R u i*R v j*R w k*a.2 w u v| ≤ 8*e := by
    have hh := abs_sum_fin_two_le (fun u => abs_sum_fin_two_le
      (fun v => abs_sum_fin_two_le (hd k i j u v)))
    convert hh using 1
    ring
  change max ‖(affineFirstJetMap R a).1‖ ‖(affineFirstJetMap R a).2‖ ≤ 8*e
  apply max_le
  · apply (pi_norm_le_iff_of_nonneg (by positivity : 0 ≤ 8*e)).mpr
    intro i
    apply (pi_norm_le_iff_of_nonneg (by positivity : 0 ≤ 8*e)).mpr
    intro j
    change ‖∑ u, ∑ v, R u i*R v j*a.1 u v‖ ≤ _
    rw [Real.norm_eq_abs]
    exact (hvsum i j).trans (by nlinarith)
  · apply (pi_norm_le_iff_of_nonneg (by positivity : 0 ≤ 8*e)).mpr
    intro k
    apply (pi_norm_le_iff_of_nonneg (by positivity : 0 ≤ 8*e)).mpr
    intro i
    apply (pi_norm_le_iff_of_nonneg (by positivity : 0 ≤ 8*e)).mpr
    intro j
    change ‖∑ u, ∑ v, ∑ w, R u i*R v j*R w k*a.2 w u v‖ ≤ 8*e
    rw [Real.norm_eq_abs]
    exact hdsum k i j

theorem inverseShearMatrix_entry_le_one {q0 : ℝ} (hq : |q0| ≤ 1) (i j : Fin 2) :
    |inverseShearMatrix q0 i j| ≤ 1 := by
  fin_cases i <;> fin_cases j <;> simp [inverseShearMatrix,hq]

theorem actual_shear_first_jet_distance_le {g h : MetricField} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hh : SmoothPositiveOn h U) (hU : IsOpen U)
    {q0 e : ℝ} (hq : |q0| ≤ 1) {p : Coord} (hp : inverseShearCoordinates q0 p ∈ U)
    (hjet : ‖actualCurvatureFirstInput g (inverseShearCoordinates q0 p)-
      actualCurvatureFirstInput h (inverseShearCoordinates q0 p)‖ ≤ e) :
    ‖actualCurvatureFirstInput (metricInShearCoordinates g q0) p-
      actualCurvatureFirstInput (metricInShearCoordinates h q0) p‖ ≤ 8*e := by
  have he : 0 ≤ e := (norm_nonneg _).trans hjet
  have hp' : affineCoordinates 0 (inverseShearMatrix q0) p ∈ U := by
    simpa only [←inverseShearCoordinates_eq_affine] using hp
  unfold metricInShearCoordinates
  rw [actualCurvatureFirstInput_affinePullback hg hU 0 (inverseShearMatrix q0) p hp',
    actualCurvatureFirstInput_affinePullback hh hU 0 (inverseShearMatrix q0) p hp',
    ←affineFirstJetMap_sub]
  exact affineFirstJetMap_norm_le_eight _ (inverseShearMatrix_entry_le_one hq) _ he
    (by simpa only [←inverseShearCoordinates_eq_affine] using hjet)

theorem actualCurvatureFirstInput_thetaPulseMetric {g : MetricField} {f : Coord → ℝ}
    {U : Set Coord} (hg : SmoothPositiveOn g U) (hf : ContDiffOn ℝ ∞ f U)
    (hU : IsOpen U) {p : Coord} (hp : p ∈ U) :
    actualCurvatureFirstInput (thetaPulseMetric g f) p =
      actualCurvatureFirstInput g p+thetaCurvatureFirstIncrement f p := by
  apply Prod.ext
  · rfl
  · exact metricFirstJet_thetaPulseMetric hg hf hU hp

theorem actual_sheared_solution_first_jet_error
    {gStar gTau : MetricField} {U : Set Coord} {q0 a delta tau e : ℝ} {N : ℕ}
    (hgStar : SmoothPositiveOn gStar U)
    (hgTest : SmoothPositiveOn (testMetric gStar q0 a N delta tau) U)
    (hgTau : SmoothPositiveOn gTau U) (hU : IsOpen U)
    (hq : |q0| ≤ 1) (ha : 0 < a) (ht : 1 ≤ tau) {p : Coord}
    (hp : inverseShearCoordinates q0 p ∈ U)
    (hjet : ‖actualCurvatureFirstInput gTau (inverseShearCoordinates q0 p)-
      actualCurvatureFirstInput (testMetric gStar q0 a N delta tau)
        (inverseShearCoordinates q0 p)‖ ≤ e) :
    ‖actualCurvatureFirstInput (metricInShearCoordinates gTau q0) p-
      actualCurvatureFirstInput (metricInShearCoordinates gStar q0) p‖ ≤
      8*e+scalarPulseFirstJetBudget a ha N delta tau := by
  have hcomp := actual_shear_first_jet_distance_le hgTau hgTest hU hq hp hjet
  let V := inverseShearCoordinates q0 ⁻¹' U
  have hV : IsOpen V := hU.preimage (inverseShearCoordinates_contDiff q0).continuous
  have hpV : p ∈ V := hp
  have hgV : SmoothPositiveOn (metricInShearCoordinates gStar q0) V := by
    simpa only [V,metricInShearCoordinates,inverseShearCoordinates_eq_affine] using
      affinePullbackMetric_smoothPositive hgStar 0 (inverseShearMatrix q0)
        (Matrix.mulVec_injective_of_isUnit (inverseShearMatrix_isUnit q0))
  have heq : actualCurvatureFirstInput
      (metricInShearCoordinates (testMetric gStar q0 a N delta tau) q0) p-
        actualCurvatureFirstInput (metricInShearCoordinates gStar q0) p =
      thetaCurvatureFirstIncrement (pulseScalar a N delta tau) p := by
    rw [metricInShearCoordinates_test,
      actualCurvatureFirstInput_thetaPulseMetric hgV (pulseScalar_contDiff a N delta tau).contDiffOn hV hpV]
    exact add_sub_cancel_left _ _
  calc
    _ ≤ ‖actualCurvatureFirstInput (metricInShearCoordinates gTau q0) p-
        actualCurvatureFirstInput (metricInShearCoordinates (testMetric gStar q0 a N delta tau) q0) p‖+
        ‖actualCurvatureFirstInput (metricInShearCoordinates (testMetric gStar q0 a N delta tau) q0) p-
          actualCurvatureFirstInput (metricInShearCoordinates gStar q0) p‖ := by
      simpa only [dist_eq_norm] using dist_triangle
        (actualCurvatureFirstInput (metricInShearCoordinates gTau q0) p)
        (actualCurvatureFirstInput (metricInShearCoordinates (testMetric gStar q0 a N delta tau) q0) p)
        (actualCurvatureFirstInput (metricInShearCoordinates gStar q0) p)
    _ ≤ _ := add_le_add hcomp (by rw [heq]; exact thetaPulse_first_increment_bound ha N delta ht p)

end SmoothLocal.Pulse

end

end OAI
