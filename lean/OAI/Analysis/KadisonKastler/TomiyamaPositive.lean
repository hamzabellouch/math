import OAI.Analysis.KadisonKastler.TomiyamaNormGeometry
import Mathlib.Analysis.CStarAlgebra.SpecialFunctions.PosPart

namespace OAI

/-! # Positivity of unital contractions

This is the first step of the norm-one projection argument.  Positivity
and adjoint preservation are derived from the norm bound and the unit.
-/

namespace KadisonKastler

noncomputable section

variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]

local instance tomiyamaSourceOrder : PartialOrder A := CStarAlgebra.spectralOrder A
local instance tomiyamaSourceStarOrder : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A
local instance tomiyamaTargetOrder : PartialOrder B := CStarAlgebra.spectralOrder B
local instance tomiyamaTargetStarOrder : StarOrderedRing B := CStarAlgebra.spectralOrderedRing B

private theorem cstar_norm_one_le (A : Type*) [CStarAlgebra A] : ‖(1 : A)‖ ≤ 1 := by
  have h : ‖star (1 : A) * (1 : A)‖ = ‖(1 : A)‖ * ‖(1 : A)‖ :=
    CStarRing.norm_star_mul_self
  simp only [star_one, one_mul] at h
  nlinarith [norm_nonneg (1 : A)]

private theorem norm_imaginary_perturbation_sq (x : A) (hx : IsSelfAdjoint x) (t : ℝ) :
    ‖1 + t • (Complex.I • x)‖ ^ 2 ≤ 1 + ‖x‖ ^ 2 * t ^ 2 := by
  have he : star (1 + t • (Complex.I • x)) * (1 + t • (Complex.I • x)) =
      1 + t ^ 2 • (star x * x) := by
    simp only [star_add, star_one, star_smul, star_trivial, Complex.star_def,
      Complex.conj_I, hx.star_eq, add_mul, mul_add, one_mul, mul_one,
      smul_mul_assoc, mul_smul_comm]
    match_scalars
    all_goals ring_nf
    all_goals norm_num [Complex.I_sq]
  calc
    ‖1 + t • (Complex.I • x)‖ ^ 2 =
        ‖star (1 + t • (Complex.I • x)) * (1 + t • (Complex.I • x))‖ := by
      rw [CStarRing.norm_star_mul_self, pow_two]
    _ = ‖1 + t ^ 2 • (star x * x)‖ := congrArg norm he
    _ ≤ ‖(1 : A)‖ + ‖t ^ 2 • (star x * x)‖ := norm_add_le _ _
    _ ≤ 1 + ‖x‖ ^ 2 * t ^ 2 := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg t),
        CStarRing.norm_star_mul_self]
      nlinarith [cstar_norm_one_le A]

/-- A unital complex-linear contraction preserves self-adjointness. -/
theorem unital_contraction_isSelfAdjoint (P : A →L[ℂ] B)
    (hP : ∀ x, ‖P x‖ ≤ ‖x‖) (h1 : P 1 = 1)
    (x : A) (hx : IsSelfAdjoint x) : IsSelfAdjoint (P x) := by
  apply isSelfAdjoint_of_quadratic_norm_bound (P x) (‖x‖ ^ 2)
  intro t
  have he : P (1 + t • (Complex.I • x)) = 1 + t • (Complex.I • P x) := by
    rw [map_add, h1, P.map_smul_of_tower, map_smul]
  calc
    ‖1 + t • (Complex.I • P x)‖ ^ 2 = ‖P (1 + t • (Complex.I • x))‖ ^ 2 := by rw [he]
    _ ≤ ‖1 + t • (Complex.I • x)‖ ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) (hP _) 2
    _ ≤ 1 + ‖x‖ ^ 2 * t ^ 2 := norm_imaginary_perturbation_sq x hx t

/-- A unital complex-linear contraction is positive. -/
theorem unital_contraction_nonneg (P : A →L[ℂ] B)
    (hP : ∀ x, ‖P x‖ ≤ ‖x‖) (h1 : P 1 = 1)
    (x : A) (hx : 0 ≤ x) : 0 ≤ P x := by
  by_cases hx0 : x = 0
  · simp only [hx0, map_zero, le_refl]
  have hn : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx0
  let y := ‖x‖⁻¹ • x
  have hy : 0 ≤ y := smul_nonneg (inv_nonneg.mpr (norm_nonneg _)) hx
  have hyn : ‖y‖ ≤ 1 := by
    simp only [y, norm_smul, Real.norm_eq_abs, abs_inv,
      abs_of_nonneg (norm_nonneg x), inv_mul_cancel₀ hn, le_refl]
  have hs := unital_contraction_isSelfAdjoint P hP h1 y hy.isSelfAdjoint
  have hdiff : ‖1 - P y‖ ≤ 1 := by
    rw [← h1, ← map_sub]
    exact (hP _).trans ((CStarAlgebra.norm_sub_le_max_of_nonneg
      (show (0 : A) ≤ 1 from zero_le_one) hy).trans
        (max_le (cstar_norm_one_le A) hyn))
  have hle : 1 - P y ≤ (1 : B) := by
    apply ((IsSelfAdjoint.one B).sub hs).le_algebraMap_norm_self.trans
    rw [Algebra.algebraMap_eq_smul_one]
    simpa only [one_smul] using
      (smul_le_smul_of_nonneg_right hdiff (show (0 : B) ≤ 1 from zero_le_one))
  have hpy : 0 ≤ P y := (sub_le_self_iff _).mp hle
  have he : P x = ‖x‖ • P y := by
    rw [← P.map_smul_of_tower]
    congr 1
    dsimp [y]
    rw [smul_smul, mul_inv_cancel₀ hn, one_smul]
  rw [he]
  exact smul_nonneg (norm_nonneg _) hpy

/-- Adjoint preservation follows from the same norm-one hypotheses. -/
theorem unital_contraction_map_star (P : A →L[ℂ] B)
    (hP : ∀ x, ‖P x‖ ≤ ‖x‖) (h1 : P 1 = 1) (x : A) :
    P (star x) = star (P x) := by
  obtain ⟨a, ha, _, hx⟩ := CStarAlgebra.exists_sum_four_nonneg x
  have hs (i : Fin 4) : star (P (a i)) = P (a i) :=
    (unital_contraction_isSelfAdjoint P hP h1 (a i) (ha i).isSelfAdjoint).star_eq
  rw [hx, star_sum, map_sum, map_sum, star_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp only [star_smul, map_smul, (ha i).star_eq, hs i]

end

end KadisonKastler

end OAI
