import OAI.GroupTheory.PolycyclicRecognition.Algebra.RationalConjugation
import Mathlib.GroupTheory.Nilpotent
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

namespace OAI

/-! # Nilpotent conjugation has a dimension-bounded unipotence exponent

On an abelian normal subgroup, conjugation minus the identity is the
commutator map. Its successive powers lie in successive lower-central terms.
Rationalization therefore gives a nilpotent operator, whose exponent is
bounded by the rational rank rather than by a chosen group nilpotency class.
-/

noncomputable section
namespace PolycyclicRecognition

open scoped IsMulCommutative TensorProduct commutatorElement

variable {G : Type} [Group G] (H : Subgroup G) [H.Normal] [IsMulCommutative H]

def integralConjugationDifference (g : G) : Module.End ℤ (Additive H) :=
  (MulAut.conjNormal (H := H) g).toAdditive.toIntLinearEquiv.toLinearMap - 1

theorem integralConjugationDifference_apply (g : G) (a : Additive H) :
    ((integralConjugationDifference H g a).toMul : G) = ⁅g, (a.toMul : G)⁆ := by
  simp only [integralConjugationDifference, LinearMap.sub_apply, Module.End.one_apply,
    commutatorElement_def]
  change (((MulAut.conjNormal (H := H) g) a.toMul / a.toMul : H) : G) = _
  rw [Subgroup.coe_div]
  change (g * (a.toMul : G) * g⁻¹) / (a.toMul : G) = _
  rw [div_eq_mul_inv]

theorem integralConjugationDifference_pow_mem (g : G) (k : ℕ) (a : Additive H) :
    (((integralConjugationDifference H g ^ k) a).toMul : G) ∈
      (⊤ : Subgroup G).lowerCentralSeries k := by
  induction k with
  | zero => exact Subgroup.mem_top _
  | succ k ih =>
    rw [pow_succ', Module.End.mul_apply, integralConjugationDifference_apply,
      Subgroup.lowerCentralSeries_succ, Subgroup.commutator_comm]
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_top g) ih

theorem integralConjugationDifference_nilpotent [Group.IsNilpotent G] (g : G) :
    IsNilpotent (integralConjugationDifference H g) := by
  refine ⟨Group.nilpotencyClass G, ?_⟩
  apply LinearMap.ext
  intro a
  have h := integralConjugationDifference_pow_mem H g (Group.nilpotencyClass G) a
  rw [Subgroup.lowerCentralSeries_nilpotencyClass, Subgroup.mem_bot] at h
  apply Additive.toMul.injective
  apply Subtype.val_injective
  exact h

theorem rationalConjugationDifference_baseChange (g : G) :
    (rationalConjugation H g).toLinearMap - 1 =
      (integralConjugationDifference H g).baseChange ℚ := by
  apply TensorProduct.AlgebraTensorModule.ext
  intro q a
  simp only [integralConjugationDifference, LinearMap.baseChange_sub,
    LinearMap.baseChange_one]
  rfl

theorem rationalConjugationDifference_nilpotent [Group.IsNilpotent G] (g : G) :
    IsNilpotent ((rationalConjugation H g).toLinearMap - 1) := by
  obtain ⟨k, hk⟩ := integralConjugationDifference_nilpotent H g
  refine ⟨k, ?_⟩
  rw [rationalConjugationDifference_baseChange, ← LinearMap.baseChange_pow,
    hk, LinearMap.baseChange_zero]

theorem nilpotentEnd_pow_finrank_eq_zero {K V : Type*} [Field K]
    [AddCommGroup V] [Module K V] [Module.Finite K V]
    {f : Module.End K V} (hf : IsNilpotent f) : f ^ Module.finrank K V = 0 := by
  obtain ⟨k, hk⟩ := hf
  apply LinearMap.ker_eq_top.mp
  apply top_unique
  calc
    ⊤ = LinearMap.ker (f ^ k) := by rw [hk, LinearMap.ker_zero]
    _ ≤ LinearMap.ker (f ^ Module.finrank K V) := Module.End.ker_pow_le_ker_pow_finrank f k

theorem rationalConjugationDifference_pow_rank [Group.IsNilpotent G]
    [Module.Finite ℚ (RationalAbelianSpace H)] (g : G) :
    ((rationalConjugation H g).toLinearMap - 1) ^
      Module.finrank ℚ (RationalAbelianSpace H) = 0 :=
  nilpotentEnd_pow_finrank_eq_zero (rationalConjugationDifference_nilpotent H g)

end PolycyclicRecognition

end

end OAI
