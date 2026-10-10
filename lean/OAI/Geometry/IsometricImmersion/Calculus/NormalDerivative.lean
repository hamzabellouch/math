import OAI.Geometry.IsometricImmersion.Immersions.NormalField
import Mathlib.Tactic.Linarith

namespace OAI

noncomputable section
open scoped ContDiff Topology BigOperators Matrix
open Filter

namespace SmoothLocal.Geometry

variable {g : MetricField} {F n : Coord → Ambient} {U : Set Coord} {p : Coord}

theorem normalField_derivative_inner_self (hn : ContDiffOn ℝ ∞ n U)
    (hunit : ∀ q ∈ U, inner ℝ (n q) (n q) = 1)
    (hU : IsOpen U) (hp : p ∈ U) (i : Fin 2) :
    inner ℝ (coordPartial i n p) (n p) = 0 := by
  have hd : DifferentiableAt ℝ n p :=
    (((hn p hp).contDiffAt (hU.mem_nhds hp)).differentiableAt (by simp))
  have heq : (fun q => inner ℝ (n q) (n q)) =ᶠ[𝓝 p]
      (fun _ : Coord => (1 : ℝ)) := by
    filter_upwards [hU.mem_nhds hp] with q hq
    exact hunit q hq
  have heq' := congrArg (fun L : Coord →L[ℝ] ℝ => L (Pi.single i 1)) heq.fderiv_eq
  rw [fderiv_inner_apply ℝ hd hd] at heq'
  simp only [fderiv_const_apply, zero_apply] at heq'
  change inner ℝ (n p) (coordPartial i n p) +
    inner ℝ (coordPartial i n p) (n p) = 0 at heq'
  rw [← real_inner_comm (n p) (coordPartial i n p)] at heq'
  linarith

theorem normalField_derivative_inner_tangent (hF : ContDiffOn ℝ ∞ F U)
    (hn : ContDiffOn ℝ ∞ n U) (hnormal : ∀ q ∈ U, IsUnitNormalAt F (n q) q)
    (hU : IsOpen U) (hp : p ∈ U) (i j : Fin 2) :
    inner ℝ (coordPartial i n p) (coordPartial j F p) =
      -secondFundamental F (n p) p i j := by
  have hdN : DifferentiableAt ℝ n p :=
    (((hn p hp).contDiffAt (hU.mem_nhds hp)).differentiableAt (by simp))
  have hdT : DifferentiableAt ℝ (coordPartial j F) p :=
    ((((partial_contDiffOn hF hU j) p hp).contDiffAt
      (hU.mem_nhds hp)).differentiableAt (by simp))
  have heq : (fun q => inner ℝ (n q) (coordPartial j F q)) =ᶠ[𝓝 p]
      (fun _ : Coord => (0 : ℝ)) := by
    filter_upwards [hU.mem_nhds hp] with q hq
    rw [real_inner_comm]
    exact (hnormal q hq).2 (Pi.single j 1)
  have heq' := congrArg (fun L : Coord →L[ℝ] ℝ => L (Pi.single i 1)) heq.fderiv_eq
  rw [fderiv_inner_apply ℝ hdN hdT] at heq'
  simp only [fderiv_const_apply, zero_apply] at heq'
  change inner ℝ (n p) (coordPartial i (coordPartial j F) p) +
    inner ℝ (coordPartial i n p) (coordPartial j F p) = 0 at heq'
  rw [← real_inner_comm (n p) (coordPartial i (coordPartial j F) p)] at heq'
  change secondFundamental F (n p) p i j +
    inner ℝ (coordPartial i n p) (coordPartial j F p) = 0 at heq'
  linarith

theorem coordPartial_normalField_eq_zero_of_secondFundamental_eq_zero
    (hg : SmoothPositiveOn g U) (hF : IsometricOn g F U)
    (hn : ContDiffOn ℝ ∞ n U) (hnormal : ∀ q ∈ U, IsUnitNormalAt F (n q) q)
    (hU : IsOpen U) (hp : p ∈ U)
    (hII : secondFundamental F (n p) p = 0) (i : Fin 2) :
    coordPartial i n p = 0 := by
  have hnt (j : Fin 2) : inner ℝ (coordPartial j F p) (n p) = 0 :=
    (hnormal p hp).2 (Pi.single j 1)
  have hwt (j : Fin 2) : inner ℝ (coordPartial j F p) (coordPartial i n p) = 0 := by
    rw [real_inner_comm, normalField_derivative_inner_tangent hF.1 hn hnormal hU hp i j]
    rw [hII]
    simp
  have hnw : inner ℝ (n p) (coordPartial i n p) = 0 := by
    rw [real_inner_comm]
    exact normalField_derivative_inner_self hn (fun q hq => (hnormal q hq).1) hU hp i
  have hspan := normal_eq_inner_smul_of_independent_tangents
    (fun j => coordPartial j F p) (isometric_tangents_independent hg hF hp)
    (n p) (coordPartial i n p) (hnormal p hp).1 hnt hwt
  simpa only [hnw, zero_smul] using hspan

theorem fderiv_normalField_eq_zero_of_secondFundamental_eq_zero
    (hg : SmoothPositiveOn g U) (hF : IsometricOn g F U)
    (hn : ContDiffOn ℝ ∞ n U) (hnormal : ∀ q ∈ U, IsUnitNormalAt F (n q) q)
    (hU : IsOpen U) (hp : p ∈ U)
    (hII : secondFundamental F (n p) p = 0) : fderiv ℝ n p = 0 := by
  apply ContinuousLinearMap.ext
  intro v
  rw [← Finset.univ_sum_single v, map_sum]
  change (∑ i : Fin 2, fderiv ℝ n p (Pi.single i (v i))) = 0
  apply Finset.sum_eq_zero
  intro i _
  have hsingle : Pi.single i (v i) = v i • Pi.single i (1 : ℝ) := by
    simpa only [smul_eq_mul, mul_one] using Pi.single_smul' i (v i) (1 : ℝ)
  rw [hsingle, map_smul]
  change v i • coordPartial i n p = 0
  rw [coordPartial_normalField_eq_zero_of_secondFundamental_eq_zero
    hg hF hn hnormal hU hp hII i, smul_zero]

theorem unitNormalField_derivative_inner_self
    (hg : SmoothPositiveOn g U) (hF : IsometricOn g F U)
    (hU : IsOpen U) (hp : p ∈ U) (i : Fin 2) :
    inner ℝ (coordPartial i (unitNormalField F) p) (unitNormalField F p) = 0 :=
  normalField_derivative_inner_self (unitNormalField_contDiffOn hg hF hU)
    (fun _ hq => unitNormalField_inner_self hg hF hq) hU hp i

theorem unitNormalField_derivative_inner_tangent
    (hg : SmoothPositiveOn g U) (hF : IsometricOn g F U)
    (hU : IsOpen U) (hp : p ∈ U) (i j : Fin 2) :
    inner ℝ (coordPartial i (unitNormalField F) p) (coordPartial j F p) =
      -secondFundamental F (unitNormalField F p) p i j :=
  normalField_derivative_inner_tangent hF.1 (unitNormalField_contDiffOn hg hF hU)
    (fun _ hq => unitNormalField_isUnitNormalAt hg hF hq) hU hp i j

theorem unitNormalField_fderiv_eq_zero_of_secondFundamental_eq_zero
    (hg : SmoothPositiveOn g U) (hF : IsometricOn g F U)
    (hU : IsOpen U) (hp : p ∈ U)
    (hII : secondFundamental F (unitNormalField F p) p = 0) :
    fderiv ℝ (unitNormalField F) p = 0 :=
  fderiv_normalField_eq_zero_of_secondFundamental_eq_zero hg hF
    (unitNormalField_contDiffOn hg hF hU)
    (fun _ hq => unitNormalField_isUnitNormalAt hg hF hq) hU hp hII

end SmoothLocal.Geometry

end

end OAI
