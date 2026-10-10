import OAI.Geometry.SurfaceImmersion.Geometry.ProjectionSingularDirection

namespace OAI

/-! The polynomial birth-and-death model for a pair of surface crosscaps.
For a negative parameter it is an immersion on the whole coordinate plane. -/
noncomputable section
open Set
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

def crosscapPairCoordinates (s : ℝ) (x : Base) : Fin 3 → ℝ :=
  ![x 0,x 0 * x 1,(x 1)^3-s*x 1]

def crosscapPairDerivative (s : ℝ) (x : Base) : Base →L[ℝ] (Fin 3 → ℝ) :=
  ContinuousLinearMap.pi ![ContinuousLinearMap.proj 0,
    x 0 • ContinuousLinearMap.proj 1 + x 1 • ContinuousLinearMap.proj 0,
    (3*(x 1)^2-s) • ContinuousLinearMap.proj 1]

lemma crosscapPairCoordinates_smooth (s : ℝ) : ContDiff ℝ ∞ (crosscapPairCoordinates s) := by
  apply contDiff_pi.mpr
  intro i
  fin_cases i <;> dsimp [crosscapPairCoordinates] <;> fun_prop

lemma crosscapPairCoordinates_hasFDerivAt (s : ℝ) (x : Base) :
    HasFDerivAt (crosscapPairCoordinates s) (crosscapPairDerivative s x) x := by
  have h0 := hasFDerivAt_apply (𝕜 := ℝ) (0 : Fin 2) x
  have h1 := hasFDerivAt_apply (𝕜 := ℝ) (1 : Fin 2) x
  apply hasFDerivAt_pi.mpr
  intro i
  fin_cases i
  · exact h0
  · exact h0.mul h1
  · change HasFDerivAt (fun y : Base => (y 1)^3-s*y 1)
      ((3*(x 1)^2-s) • ContinuousLinearMap.proj 1) x
    convert (h1.pow 3).sub (h1.const_mul s) using 1
    apply ContinuousLinearMap.ext
    intro v
    simp
    ring

lemma crosscapPairDerivative_injective_iff (s : ℝ) (x : Base) :
    Function.Injective (crosscapPairDerivative s x) ↔ x 0 ≠ 0 ∨ 3*(x 1)^2-s ≠ 0 := by
  constructor
  · intro h
    by_contra hn
    push Not at hn
    have he : crosscapPairDerivative s x (![0,1] : Base) = crosscapPairDerivative s x 0 := by
      ext i
      fin_cases i <;> simp [crosscapPairDerivative,hn.1,hn.2]
    have hh := congrFun (h he) 1
    norm_num at hh
  · intro h v w he
    have h0 : v 0 = w 0 := congrFun he 0
    have h1 : x 0 * v 1 + x 1 * v 0 = x 0 * w 1 + x 1 * w 0 := congrFun he 1
    have h2 : (3*(x 1)^2-s)*v 1 = (3*(x 1)^2-s)*w 1 := congrFun he 2
    have hvw : v 1 = w 1 := by
      rcases h with h | h
      · rw [h0] at h1
        exact mul_left_cancel₀ h (add_right_cancel h1)
      · exact mul_left_cancel₀ h h2
    ext i
    fin_cases i
    · exact h0
    · exact hvw

lemma crosscapPairCoordinates_singular_iff (s : ℝ) (x : Base) :
    ¬ Function.Injective (fderiv ℝ (crosscapPairCoordinates s) x) ↔
      x 0 = 0 ∧ 3*(x 1)^2 = s := by
  rw [(crosscapPairCoordinates_hasFDerivAt s x).fderiv,crosscapPairDerivative_injective_iff]
  push Not
  exact and_congr Iff.rfl sub_eq_zero

def crosscapPair (s : ℝ) : Base → ProjectionTarget 3 :=
  (EuclideanSpace.equiv (Fin 3) ℝ).symm ∘ crosscapPairCoordinates s

lemma crosscapPair_smooth (s : ℝ) : ContDiff ℝ ∞ (crosscapPair s) :=
  (EuclideanSpace.equiv (Fin 3) ℝ).symm.contDiff.comp (crosscapPairCoordinates_smooth s)

theorem crosscapPair_immersion_of_negative {s : ℝ} (hs : s < 0) (x : Base) :
    Function.Injective (fderiv ℝ (crosscapPair s) x) := by
  have hI : Function.Injective (crosscapPairDerivative s x) :=
    (crosscapPairDerivative_injective_iff s x).mpr (Or.inr (by nlinarith [sq_nonneg (x 1)]))
  rw [crosscapPair,fderiv_comp x
    (EuclideanSpace.equiv (Fin 3) ℝ).symm.differentiableAt
    ((crosscapPairCoordinates_smooth s).differentiable (by simp) x),
    (EuclideanSpace.equiv (Fin 3) ℝ).symm.fderiv,
    (crosscapPairCoordinates_hasFDerivAt s x).fderiv]
  exact (EuclideanSpace.equiv (Fin 3) ℝ).symm.injective.comp hI

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
