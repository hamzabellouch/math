import OAI.Algebra.Finitistic.Bar.LeadingSuffixFaces
import OAI.Algebra.Finitistic.Bar.BarFunctor

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

variable (W : Type u) [AddCommGroup W] [Module k W] [Module D W] [IsScalarTower k D W]

omit [Module A N] [IsScalarTower k A N] in
/-- Inserting D slots commutes with every actual vertical map of suffix modules. -/
theorem suffixEmbed_termMap (s n : ℕ) (e : W →ₗ[k] term k A N s)
    (f : M →ₗ[D] W) (v : term k D M n) :
    suffixEmbed k D X N W s e n (termMap k D M W f n v) =
    suffixEmbed k D X N M s (e.comp (f.restrictScalars k)) n v := by
  induction n with
  | zero => rfl
  | succ n ih =>
    induction v using TensorProduct.inductionOn with
    | tmul d v =>
      rw [termMap_tmul, suffixEmbed_tmul, suffixEmbed_tmul, ih]
    | add v w hv hw => simp only [map_add, hv, hw]

omit [Module A N] [IsScalarTower k A N] in
/-- X coefficients commute with the same vertical suffix maps. -/
theorem idealSuffixEmbed_termMap (s n : ℕ) (e : W →ₗ[k] term k A N s)
    (f : M →ₗ[D] W) (v : X ⊗[k] term k D M n) :
    idealSuffixEmbed k D X N W s n e
      (AlgebraTensorModule.lTensor D X ((termMap k D M W f n).restrictScalars k) v) =
    idealSuffixEmbed k D X N M s n (e.comp (f.restrictScalars k)) v := by
  induction v using TensorProduct.inductionOn with
  | tmul x v =>
    rw [AlgebraTensorModule.lTensor_tmul, idealSuffixEmbed_tmul, idealSuffixEmbed_tmul]
    change (inr x : A) ⊗ₜ[k] suffixEmbed k D X N W s e n (termMap k D M W f n v) = _
    rw [suffixEmbed_termMap]
  | add v w hv hw => simp only [map_add, hv, hw]

omit [Module A N] [IsScalarTower k A N] in
/-- Exterior D coefficients commute with all vertical suffix maps. -/
theorem outerSuffixEmbed_termMap (s n : ℕ) (e : W →ₗ[k] term k A N s)
    (f : M →ₗ[D] W) (v : D ⊗[k] term k D M n) :
    outerSuffixEmbed k D X N W s n e (termMap k D M W f (n+1) v) =
    outerSuffixEmbed k D X N M s n (e.comp (f.restrictScalars k)) v := by
  induction v using TensorProduct.inductionOn with
  | tmul d v =>
    rw [termMap_tmul, outerSuffixEmbed_tmul, outerSuffixEmbed_tmul, suffixEmbed_termMap]
  | add v w hv hw => simp only [map_add, hv, hw]

omit [Module D M] [IsScalarTower k D M] [Module A N] [IsScalarTower k A N] in
/-- The prefix construction is additive in the whole suffix map. -/
theorem suffixEmbed_add_map (s n : ℕ) (e f : M →ₗ[k] term k A N s)
    (v : term k D M n) :
    suffixEmbed k D X N M s (e+f) n v =
      suffixEmbed k D X N M s e n v + suffixEmbed k D X N M s f n v := by
  induction n with
  | zero => rfl
  | succ n ih =>
    induction v using TensorProduct.inductionOn with
    | tmul d v =>
      rw [suffixEmbed_tmul, suffixEmbed_tmul, suffixEmbed_tmul, ih, TensorProduct.tmul_add]
    | add v w hv hw => simp only [map_add, hv, hw]; abel

omit [Module D M] [IsScalarTower k D M] [Module A N] [IsScalarTower k A N] in
/-- Scalar totalization signs pass through the unchanged tensor prefix. -/
theorem suffixEmbed_smul_map (s n : ℕ) (a : k) (e : M →ₗ[k] term k A N s)
    (v : term k D M n) :
    suffixEmbed k D X N M s (a • e) n v = a • suffixEmbed k D X N M s e n v := by
  induction n with
  | zero => rfl
  | succ n ih =>
    induction v using TensorProduct.inductionOn with
    | tmul d v =>
      rw [suffixEmbed_tmul, suffixEmbed_tmul, ih]
      exact TensorProduct.tmul_smul _ _ _
    | add v w hv hw => simp only [map_add, hv, hw, smul_add]

/-- A genuine linear operation on suffix maps, so finite sums distribute exactly. -/
def suffixEmbedLinear (s n : ℕ) :
    (M →ₗ[k] term k A N s) →ₗ[k] (term k D M n →ₗ[k] term k A N (s+n)) where
  toFun e := suffixEmbed k D X N M s e n
  map_add' e f := by
    ext v
    exact suffixEmbed_add_map k D X N M s n e f v
  map_smul' a e := by
    ext v
    exact suffixEmbed_smul_map k D X N M s n a e v

omit [Module D M] [IsScalarTower k D M] [Module A N] [IsScalarTower k A N] in
/-- The actual finite-sum distribution needed for an arbitrary recursive suffix differential. -/
theorem suffixEmbed_sum {I : Type*} (S : Finset I) (s n : ℕ)
    (e : I → M →ₗ[k] term k A N s) (v : term k D M n) :
    suffixEmbed k D X N M s (∑ i ∈ S, e i) n v =
      ∑ i ∈ S, suffixEmbed k D X N M s (e i) n v := by
  change suffixEmbedLinear k D X N M s n (∑ i ∈ S, e i) v = _
  rw [map_sum, LinearMap.sum_apply]
  rfl

/-- Mathlib's unit-valued totalization sign is exactly the field-valued sign. -/
theorem totalSign_smul (n : ℕ) (v : M) :
    ((-1 : ℤˣ)^n) • v = (-1 : k)^n • v := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hu : (-1 : ℤˣ) • v = -v := by
      change (-1 : ℤ) • v = -v
      exact neg_one_zsmul v
    simpa only [pow_succ, mul_smul, hu, neg_one_smul, smul_neg] using congrArg Neg.neg ih
end DerivedBar.ParityBridge

end

end OAI
