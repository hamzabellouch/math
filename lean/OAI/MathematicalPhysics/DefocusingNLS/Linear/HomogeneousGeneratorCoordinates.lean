import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousGeneratorPerturbation
import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousGeneratorEigenvector
import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousComplexSemigroup
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul

namespace OAI

/-! # Finite generator eigenvectors in the actual evolution domain

An eigenvector on the finite contour space evolves by its scalar
exponential. Its two real coordinates therefore belong to the free
generator domain and satisfy the exact bounded-potential equations.
-/

open Set
open scoped NNReal

namespace DefocusingNLS

attribute [local irreducible] homogeneousFreeOperator

section Abstract

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

omit [CompleteSpace E] in
theorem projectionSemigroup_eigenvector (S : ℝ≥0 → E →L[ℂ] E)
    (Q : E →L[ℂ] E) (hcomm : ∀ t, Commute (S t) Q)
    (hfin : FiniteDimensional ℂ Q.range) (G : Q.range →L[ℂ] Q.range)
    (hG : ∀ t, projectionSemigroupRestriction S Q hcomm t = NormedSpace.exp ((t : ℝ) • G))
    (lam : ℂ) (u : Q.range) (hu : G u = lam • u) (t : ℝ≥0) :
    S t (u : E) = Complex.exp (((t : ℝ) : ℂ) * lam) • (u : E) := by
  let : FiniteDimensional ℂ Q.range := hfin
  let : CompleteSpace Q.range := FiniteDimensional.complete ℂ Q.range
  have he := congrArg (fun L : Q.range →L[ℂ] Q.range => (L u : E)) (hG t)
  change S t (u : E) = (NormedSpace.exp ((t : ℝ) • G) u : E) at he
  rw [real_smul_operator_exp_apply_of_eigenvector G lam u hu] at he
  exact he

omit [CompleteSpace E] in
theorem hasDerivWithinAt_semigroup_eigenvector
    (S : ℝ≥0 → E →L[ℂ] E) (lam : ℂ) (u : E)
    (hu : ∀ t : ℝ≥0, S t u = Complex.exp (((t : ℝ) : ℂ) * lam) • u) :
    HasDerivWithinAt (fun t : ℝ => S t.toNNReal u) (lam • u) (Ici 0) 0 := by
  have he : HasDerivAt (fun t : ℝ => Complex.exp ((t : ℂ) * lam)) lam 0 := by
    simpa only [Complex.real_smul, zero_smul, NormedSpace.exp_zero, one_mul,
      ← Complex.exp_eq_exp_ℂ] using (hasDerivAt_exp_smul_const (𝕂 := ℝ) lam (0 : ℝ))
  apply (he.smul_const u).hasDerivWithinAt.congr
  · intro t ht
    simpa only [Real.coe_toNNReal t ht] using hu t.toNNReal
  · simpa only [Real.toNNReal_zero, NNReal.coe_zero, Complex.ofReal_zero,
      zero_mul, Complex.exp_zero, one_smul] using hu 0

end Abstract

section Actual

variable (a b k : ℝ) (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k)
  (m : ℕ) (q : HomogeneousY a k)

local notation "H" => HomogeneousY a k
local notation "X" => homogeneousComplexReal a k ha ha1 hk
local notation "Y" => homogeneousComplexImag a k ha ha1 hk
local notation "B" => homogeneousLinearizedPotential a k ha ha1 hk m q
local notation "S" => homogeneousComplexLinearizedStep a b k ha ha1 hk m q

theorem homogeneous_eigenvector_free_coordinates (lam : ℂ) (u : H × H)
    (hu : ∀ t : ℝ≥0, S t u = Complex.exp (((t : ℝ) : ℂ) * lam) • u) :
    HasDerivWithinAt (fun t : ℝ => homogeneousFreeOperator a b k t ha ha1 hk (X u))
        (X (lam • u) - B (X u)) (Ici 0) 0 ∧
      HasDerivWithinAt (fun t : ℝ => homogeneousFreeOperator a b k t ha ha1 hk (Y u))
        (Y (lam • u) - B (Y u)) (Ici 0) 0 := by
  have hd := hasDerivWithinAt_semigroup_eigenvector S lam u hu
  have hX := (X).hasFDerivAt.comp_hasDerivWithinAt 0 hd
  have hY := (Y).hasFDerivAt.comp_hasDerivWithinAt 0 hd
  have hx : HasDerivWithinAt (fun t : ℝ =>
      homogeneousLinearizedStep a b k ha ha1 hk m q t.toNNReal (X u))
      (X (lam • u)) (Ici 0) 0 := by
    simpa only [Function.comp_def, homogeneousComplexLinearizedStep,
      homogeneousComplexification_real] using hX
  have hy : HasDerivWithinAt (fun t : ℝ =>
      homogeneousLinearizedStep a b k ha ha1 hk m q t.toNNReal (Y u))
      (Y (lam • u)) (Ici 0) 0 := by
    simpa only [Function.comp_def, homogeneousComplexLinearizedStep,
      homogeneousComplexification_imag] using hY
  exact ⟨homogeneousFree_derivWithin_of_linearized a b k ha ha1 hk m q _ _ hx,
    homogeneousFree_derivWithin_of_linearized a b k ha ha1 hk m q _ _ hy⟩

end Actual

end DefocusingNLS

end OAI
