import OAI.Geometry.IsometricImmersion.Metrics.MetricCompatibility

namespace OAI

noncomputable section
open scoped ContDiff Topology BigOperators Matrix
open Filter

namespace SmoothLocal.Geometry

namespace MetricJetCalculus

theorem coordPartial_const_mul_at {f : Coord → ℝ} {p : Coord}
    (hf : DifferentiableAt ℝ f p) (c : ℝ) (i : Fin 2) :
    coordPartial i (fun q => c * f q) p = c * coordPartial i f p := by
  simp [coordPartial, fderiv_const_mul hf]

end MetricJetCalculus

theorem metric_inverse_derivative_identity {g : MetricField} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) {p : Coord} (hp : p ∈ U)
    (d i j : Fin 2) :
    (∑ a, (coordPartial d (fun q => g q i a) p * inverseMetric g p a j +
      g p i a * coordPartial d (fun q => inverseMetric g q a j) p)) = 0 := by
  have hproduct : (fun q => ∑ a, g q i a * inverseMetric g q a j) =ᶠ[𝓝 p]
      (fun _ => (1 : Matrix (Fin 2) (Fin 2) ℝ) i j) := by
    filter_upwards [hU.mem_nhds hp] with q hq
    exact congrFun (congrFun
      (Matrix.mul_nonsing_inv (g q) ((Matrix.isUnit_iff_isUnit_det _).mp (hg.2 q hq).isUnit)) i) j
  have hdg (a : Fin 2) : DifferentiableAt ℝ (fun q => g q i a) p :=
    (((hg.1 i a) p hp).contDiffAt (hU.mem_nhds hp)).differentiableAt (by simp)
  have hdi (a : Fin 2) : DifferentiableAt ℝ (fun q => inverseMetric g q a j) p :=
    (((inverseMetric_contDiffOn hg a j) p hp).contDiffAt
      (hU.mem_nhds hp)).differentiableAt (by simp)
  have hzero : coordPartial d (fun q => ∑ a, g q i a * inverseMetric g q a j) p = 0 := by
    unfold coordPartial
    rw [hproduct.fderiv_eq]
    simp
  have hmul (a : Fin 2) : DifferentiableAt ℝ
      (fun q => g q i a * inverseMetric g q a j) p := (hdg a).mul (hdi a)
  rw [HessianCalculus.coordPartial_sum_two _ hmul d] at hzero
  simpa only [HessianCalculus.coordPartial_mul_at (hdg _) (hdi _) d] using hzero

theorem inverseMetric_coordPartial_eq_of_firstJet
    {g h : MetricField} {U : Set Coord} {p : Coord}
    (hg : SmoothPositiveOn g U) (hh : SmoothPositiveOn h U) (hU : IsOpen U)
    (hp : p ∈ U) (hval : g p = h p)
    (hfirst : ∀ d i j, coordPartial d (fun q => g q i j) p =
      coordPartial d (fun q => h q i j) p) (d i j : Fin 2) :
    coordPartial d (fun q => inverseMetric g q i j) p =
      coordPartial d (fun q => inverseMetric h q i j) p := by
  have hinv : inverseMetric g p = inverseMetric h p := by simp only [inverseMetric, hval]
  have hvec : g p *ᵥ (fun a => coordPartial d (fun q => inverseMetric g q a j) p) =
      g p *ᵥ (fun a => coordPartial d (fun q => inverseMetric h q a j) p) := by
    ext a
    have hleft := metric_inverse_derivative_identity hg hU hp d a j
    have hright := metric_inverse_derivative_identity hh hU hp d a j
    simp only [hval, hfirst, hinv, Fin.sum_univ_two] at hleft
    simp only [Fin.sum_univ_two] at hright
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, hval]
    linarith
  exact congrFun (Matrix.mulVec_injective_of_isUnit (hg.2 p hp).isUnit hvec) i

theorem christoffel_coordPartial_formula {g : MetricField} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) {p : Coord} (hp : p ∈ U)
    (d k i j : Fin 2) :
    coordPartial d (christoffel g k i j) p = (1 / 2 : ℝ) * ∑ l,
      (coordPartial d (fun q => inverseMetric g q k l) p *
        (coordPartial i (fun q => g q j l) p + coordPartial j (fun q => g q i l) p -
          coordPartial l (fun q => g q i j) p) +
        inverseMetric g p k l *
          (coordPartial d (coordPartial i (fun q => g q j l)) p +
            coordPartial d (coordPartial j (fun q => g q i l)) p -
            coordPartial d (coordPartial l (fun q => g q i j)) p)) := by
  have hdg (a b c : Fin 2) : DifferentiableAt ℝ (coordPartial a (fun q => g q b c)) p :=
    (((partial_contDiffOn (hg.1 b c) hU a) p hp).contDiffAt
      (hU.mem_nhds hp)).differentiableAt (by simp)
  have hdi (l : Fin 2) : DifferentiableAt ℝ (fun q => inverseMetric g q k l) p :=
    (((inverseMetric_contDiffOn hg k l) p hp).contDiffAt
      (hU.mem_nhds hp)).differentiableAt (by simp)
  let B : Fin 2 → Coord → ℝ := fun l q =>
    coordPartial i (fun q => g q j l) q + coordPartial j (fun q => g q i l) q -
      coordPartial l (fun q => g q i j) q
  have hB (l : Fin 2) : DifferentiableAt ℝ (B l) p :=
    ((hdg i j l).add (hdg j i l)).sub (hdg l i j)
  have hDB (l : Fin 2) : coordPartial d (B l) p =
      coordPartial d (coordPartial i (fun q => g q j l)) p +
        coordPartial d (coordPartial j (fun q => g q i l)) p -
        coordPartial d (coordPartial l (fun q => g q i j)) p := by
    change coordPartial d (fun q =>
      (coordPartial i (fun q => g q j l) q + coordPartial j (fun q => g q i l) q) -
        coordPartial l (fun q => g q i j) q) p = _
    have hadd : DifferentiableAt ℝ
        (fun q => coordPartial i (fun q => g q j l) q + coordPartial j (fun q => g q i l) q) p :=
      (hdg i j l).add (hdg j i l)
    rw [HessianCalculus.coordPartial_sub_at hadd (hdg l i j) d,
      HessianCalculus.coordPartial_add_at (hdg i j l) (hdg j i l) d]
  have hsum : DifferentiableAt ℝ (fun q => ∑ l, inverseMetric g q k l * B l q) p :=
    DifferentiableAt.fun_sum fun l _ => (hdi l).mul (hB l)
  change coordPartial d (fun q => (1 / 2 : ℝ) * ∑ l, inverseMetric g q k l * B l q) p = _
  have hterm (l : Fin 2) : DifferentiableAt ℝ
      (fun q => inverseMetric g q k l * B l q) p := (hdi l).mul (hB l)
  rw [MetricJetCalculus.coordPartial_const_mul_at hsum _ d,
    HessianCalculus.coordPartial_sum_two _ hterm d]
  simp only [HessianCalculus.coordPartial_mul_at (hdi _) (hB _) d, hDB, B]

theorem christoffel_eq_of_firstJet {g h : MetricField} {p : Coord}
    (hval : g p = h p)
    (hfirst : ∀ d i j, coordPartial d (fun q => g q i j) p =
      coordPartial d (fun q => h q i j) p) (k i j : Fin 2) :
    christoffel g k i j p = christoffel h k i j p := by
  simp only [christoffel, inverseMetric, hval, hfirst]

theorem christoffel_coordPartial_eq_of_twoJet
    {g h : MetricField} {U : Set Coord} {p : Coord}
    (hg : SmoothPositiveOn g U) (hh : SmoothPositiveOn h U) (hU : IsOpen U)
    (hp : p ∈ U) (hval : g p = h p)
    (hfirst : ∀ d i j, coordPartial d (fun q => g q i j) p =
      coordPartial d (fun q => h q i j) p)
    (hsecond : ∀ d e i j, coordPartial d (coordPartial e (fun q => g q i j)) p =
      coordPartial d (coordPartial e (fun q => h q i j)) p) (d k i j : Fin 2) :
    coordPartial d (christoffel g k i j) p = coordPartial d (christoffel h k i j) p := by
  have hInvD := inverseMetric_coordPartial_eq_of_firstJet hg hh hU hp hval hfirst
  simp only [inverseMetric] at hInvD
  rw [christoffel_coordPartial_formula hg hU hp d k i j,
    christoffel_coordPartial_formula hh hU hp d k i j]
  simp only [hInvD, hfirst, hsecond, inverseMetric, hval]

theorem gaussianCurvature_eq_of_twoJet
    {g h : MetricField} {U : Set Coord} {p : Coord}
    (hg : SmoothPositiveOn g U) (hh : SmoothPositiveOn h U) (hU : IsOpen U)
    (hp : p ∈ U) (hval : g p = h p)
    (hfirst : ∀ d i j, coordPartial d (fun q => g q i j) p =
      coordPartial d (fun q => h q i j) p)
    (hsecond : ∀ d e i j, coordPartial d (coordPartial e (fun q => g q i j)) p =
      coordPartial d (coordPartial e (fun q => h q i j)) p) :
    gaussianCurvature g p = gaussianCurvature h p := by
  have hΓ := christoffel_eq_of_firstJet hval hfirst
  have hDΓ := christoffel_coordPartial_eq_of_twoJet hg hh hU hp hval hfirst hsecond
  simp only [gaussianCurvature, riemann, hΓ, hDΓ, hval]

end SmoothLocal.Geometry

end

end OAI
