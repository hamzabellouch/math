import OAI.Algebra.Finitistic.Bar.SuffixParityFaces

namespace OAI
open CategoryTheory TensorProduct TrivSqZeroExt
open scoped TensorProduct
noncomputable section
namespace DerivedBar.ParityBridge
universe u
variable (k D X N : Type u) [Field k] [Ring D] [Algebra k D]
  [AddCommGroup X] [Module k X] [Module D X] [Module Dᵐᵒᵖ X]
  [SMulCommClass D Dᵐᵒᵖ X] [IsScalarTower k D X] [IsScalarTower k Dᵐᵒᵖ X]
  [AddCommGroup N] [Module k N]
local notation "A" => TrivSqZeroExt D X

variable (M : Type u) [AddCommGroup M] [Module k M] [Module D M]
  [IsScalarTower k D M]
variable [Module (TrivSqZeroExt D X) N] [IsScalarTower k (TrivSqZeroExt D X) N]

/-- Retain the exterior D coefficient while inserting an arbitrary suffix. -/
def outerSuffixEmbed (s n : ℕ) (e : M →ₗ[k] term k A N s) :
    D ⊗[k] term k D M n →ₗ[D] D ⊗[k] term k A N (s+n) :=
  AlgebraTensorModule.lTensor D D (suffixEmbed k D X N M s e n)

omit [Module D M] [IsScalarTower k D M] [Module A N] [IsScalarTower k A N] in
@[simp] theorem outerSuffixEmbed_tmul (s n : ℕ) (e : M →ₗ[k] term k A N s)
    (d : D) (v : term k D M n) :
    outerSuffixEmbed k D X N M s n e (d ⊗ₜ[k] v) =
      d ⊗ₜ[k] suffixEmbed k D X N M s e n v := rfl

omit [Module D M] [IsScalarTower k D M] [Module A N] [IsScalarTower k A N] in
/-- The projected leading face is exactly the original D multiplication. -/
theorem coefficient_suffixEmbed (s n : ℕ) (e : M →ₗ[k] term k A N s)
    (v : term k D M (n+1)) :
    FreeBaseChange.coefficient (fstHom k D X) (term k A N (s+n))
      (suffixEmbed k D X N M s e (n+1) v) = outerSuffixEmbed k D X N M s n e v := by
  induction v using TensorProduct.inductionOn with
  | tmul d v =>
    rw [suffixEmbed_tmul, FreeBaseChange.coefficient_tmul]
    rfl
  | add v w hv hw => simp only [map_add, hv, hw]

/-- Exterior D comparison with the genuine free-bar differential and all later
suffix faces. Negating the suffix differential gives the total sign (-1)^i. -/
theorem parity_outerSuffixEmbed (s n : ℕ) (e : M →ₗ[k] term k A N (s+1))
    (he : ∀ (d : D) (v : M), e (d • v) = (inl d : A) • e v)
    (v : D ⊗[k] term k D M (n+1)) :
    SquareZero.multibarTwoSidedDifferential k D X N ((s+1)+n)
      (outerSuffixEmbed k D X N M (s+1) (n+1) e v) =
    outerSuffixEmbed k D X N M (s+1) n e (DerivedBar.differential k D M (n+1) v) +
      (-1 : k)^n • AlgebraTensorModule.lTensor D D
        (termCast k D X N (show s+(n+1)=(s+1)+n by omega))
        (outerSuffixEmbed k D X N M s (n+1)
          ((SquareZero.multibarAugmentedDifferential k D X N s).comp e) v) := by
  induction v using TensorProduct.inductionOn with
  | tmul d v =>
    rw [outerSuffixEmbed_tmul, SquareZero.multibarTwoSidedDifferential_tmul,
      coefficient_suffixEmbed, parity_suffixEmbed k D X N M s n e he,
      DerivedBar.differential_succ_tmul, map_sub, map_smul, outerSuffixEmbed_tmul,
      outerSuffixEmbed_tmul, AlgebraTensorModule.lTensor_tmul]
    erw [TensorProduct.tmul_add, TensorProduct.tmul_smul]
    have hs : (-1 : k)^(n+1) = -((-1 : k)^n) := by rw [pow_succ, mul_neg_one]
    rw [hs]
    have hn : (-((-1 : k)^n)) •
        (d ⊗ₜ[k] termCast k D X N (show s+(n+1)=(s+1)+n by omega)
          (suffixEmbed k D X N M s ((SquareZero.multibarAugmentedDifferential k D X N s).comp e) (n+1) v)) =
        -(((-1 : k)^n) • (d ⊗ₜ[k] termCast k D X N (show s+(n+1)=(s+1)+n by omega)
          (suffixEmbed k D X N M s ((SquareZero.multibarAugmentedDifferential k D X N s).comp e) (n+1) v))) :=
      _root_.neg_smul ((-1:k)^n)
        (d ⊗ₜ[k] termCast k D X N (show s+(n+1)=(s+1)+n by omega)
          (suffixEmbed k D X N M s ((SquareZero.multibarAugmentedDifferential k D X N s).comp e) (n+1) v))
    rw [hn]
    abel
  | add v w hv hw => simp only [map_add, hv, hw, smul_add]; abel

omit [Module D M] [IsScalarTower k D M] in
/-- At a zero-length leading D block the projected X endpoint is zero. -/
theorem parity_outerSuffixEmbed_zero (s : ℕ) (e : M →ₗ[k] term k A N (s+1))
    (he : ∀ v, FreeBaseChange.coefficient (fstHom k D X) (term k A N s) (e v) = 0)
    (v : D ⊗[k] M) :
    SquareZero.multibarTwoSidedDifferential k D X N s
      (outerSuffixEmbed k D X N M (s+1) 0 e v) =
    -outerSuffixEmbed k D X N M s 0
      ((SquareZero.multibarAugmentedDifferential k D X N s).comp e) v := by
  induction v using TensorProduct.inductionOn with
  | tmul d v =>
    rw [outerSuffixEmbed_tmul, SquareZero.multibarTwoSidedDifferential_tmul]
    change d • FreeBaseChange.coefficient (fstHom k D X) (term k A N s) (e v) -
      d ⊗ₜ[k] SquareZero.multibarAugmentedDifferential k D X N s (e v) = _
    rw [he, smul_zero, zero_sub]
    rfl
  | add v w hv hw => simp only [map_add, hv, hw, neg_add]
end DerivedBar.ParityBridge

end

end OAI
