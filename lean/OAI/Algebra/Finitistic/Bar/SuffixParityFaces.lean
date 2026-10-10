import OAI.Algebra.Finitistic.Bar.InflatedParityFaces

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

/-- Explicit degree transport; it changes no tensor factor or action. -/
def termCast {a b : ℕ} (h : a=b) : term k A N a →ₗ[k] term k A N b := by
  subst b
  exact LinearMap.id

@[simp] theorem termCast_refl (a : ℕ) (v : term k A N a) :
    termCast k D X N (rfl : a=a) v = v := rfl

theorem termCast_tmul {a b : ℕ} (h : a=b) (h' : a+1=b+1)
    (x : A) (v : term k A N a) :
    termCast k D X N h' (x ⊗ₜ[k] v) = x ⊗ₜ[k] termCast k D X N h v := by
  subst b
  rfl

variable (M : Type u) [AddCommGroup M] [Module k M] [Module D M]
  [IsScalarTower k D M]

/-- Insert any D block before an arbitrary linear suffix, preserving its tensor order. -/
def suffixEmbed (s : ℕ) (e : M →ₗ[k] term k A N s) :
    (n : ℕ) → term k D M n →ₗ[k] term k A N (s+n)
  | 0 => e
  | n+1 => TensorProduct.map (inlAlgHom k D X).toLinearMap (suffixEmbed s e n)

omit [Module D M] [IsScalarTower k D M] in
@[simp] theorem suffixEmbed_tmul (s n : ℕ) (e : M →ₗ[k] term k A N s)
    (d : D) (v : term k D M n) :
    suffixEmbed k D X N M s e (n+1) (d ⊗ₜ[k] v) =
      (inl d : A) ⊗ₜ[k] suffixEmbed k D X N M s e n v := rfl

variable [Module (TrivSqZeroExt D X) N] [IsScalarTower k (TrivSqZeroExt D X) N]

omit [IsScalarTower k D M] [IsScalarTower k A N] in
theorem suffixEmbed_smul (s n : ℕ) (e : M →ₗ[k] term k A N s)
    (he : ∀ (d : D) (v : M), e (d • v) = (inl d : A) • e v)
    (d : D) (v : term k D M n) :
    suffixEmbed k D X N M s e n (d • v) =
      (inl d : A) • suffixEmbed k D X N M s e n v := by
  cases n with
  | zero => exact he d v
  | succ n =>
    induction v using TensorProduct.inductionOn with
    | tmul b v =>
      change (inl (d*b) : A) ⊗ₜ[k] _ = ((inl d : A)*inl b) ⊗ₜ[k] _
      rw [inl_mul_inl]
    | add v w hv hw => simp only [smul_add, map_add, hv, hw]

/-- General D-block comparison, including the differential of an arbitrary
positive-length suffix. The second term is the totalization sign, not zero. -/
theorem parity_suffixEmbed (s n : ℕ) (e : M →ₗ[k] term k A N (s+1))
    (he : ∀ (d : D) (v : M), e (d • v) = (inl d : A) • e v)
    (v : term k D M (n+1)) :
    SquareZero.multibarAugmentedDifferential k D X N ((s+1)+n)
      (suffixEmbed k D X N M (s+1) e (n+1) v) =
    suffixEmbed k D X N M (s+1) e n (DerivedBar.differential k D M n v) +
      (-1 : k)^(n+1) • termCast k D X N (show s+(n+1)=(s+1)+n by omega)
        (suffixEmbed k D X N M s
          ((SquareZero.multibarAugmentedDifferential k D X N s).comp e) (n+1) v) := by
  induction n with
  | zero =>
    induction v using TensorProduct.inductionOn with
    | tmul d v =>
      rw [suffixEmbed_tmul, SquareZero.multibarAugmentedDifferential_succ,
        SquareZero.slotParity_base, DerivedBar.differential_zero_tmul,
        suffixEmbed_tmul]
      change (inl d : A) • e v - (inl d : A) ⊗ₜ[k] _ = e (d • v) + (-1:k)^1 • _
      rw [he]
      simp only [pow_one, neg_one_smul, sub_eq_add_neg]
      rfl
    | add v w hv hw => simp only [map_add, hv, hw, smul_add]; abel
  | succ n ih =>
    induction v using TensorProduct.inductionOn with
    | tmul d v =>
      rw [suffixEmbed_tmul]
      change SquareZero.slotParity k D X (inl d) • suffixEmbed k D X N M (s+1) e (n+1) v -
        SquareZero.slotParity k D X (inl d) ⊗ₜ[k]
          SquareZero.multibarAugmentedDifferential k D X N (s+1+n)
            (suffixEmbed k D X N M (s+1) e (n+1) v) = _
      rw [SquareZero.slotParity_base, ih, DerivedBar.differential_succ_tmul,
        map_sub, suffixEmbed_smul k D X N M (s+1) (n+1) e he,
        suffixEmbed_tmul, suffixEmbed_tmul]
      erw [termCast_tmul k D X N (show s+(n+1)=(s+1)+n by omega)
          (show (s+(n+1))+1=((s+1)+n)+1 by omega) (inl d)
          (suffixEmbed k D X N M s ((SquareZero.multibarAugmentedDifferential k D X N s).comp e) (n+1) v)]
      erw [TensorProduct.tmul_add, TensorProduct.tmul_smul]
      have hs : (-1 : k)^(n+1+1) = -((-1 : k)^(n+1)) := by
        rw [pow_succ, mul_neg_one]
      rw [hs]
      erw [neg_smul]
      abel
    | add v w hv hw => simp only [map_add, hv, hw, smul_add]; abel


/-- Literal X coefficient followed by any D block and any recursive suffix. -/
def idealSuffixEmbed (s n : ℕ) (e : M →ₗ[k] term k A N s) :
    X ⊗[k] term k D M n →ₗ[k] term k A N ((s+n)+1) :=
  TensorProduct.map ((inrHom D X).restrictScalars k) (suffixEmbed k D X N M s e n)

omit [Module D M] [IsScalarTower k D M] [Module A N] [IsScalarTower k A N] in
@[simp] theorem idealSuffixEmbed_tmul (s n : ℕ) (e : M →ₗ[k] term k A N s)
    (x : X) (v : term k D M n) :
    idealSuffixEmbed k D X N M s n e (x ⊗ₜ[k] v) =
      (inr x : A) ⊗ₜ[k] suffixEmbed k D X N M s e n v := rfl

omit [Module D M] [IsScalarTower k D M] [Module A N] [IsScalarTower k A N] in
/-- The original right D action supplies the first face for every suffix. -/
theorem ideal_action_suffixEmbed (s n : ℕ) (e : M →ₗ[k] term k A N s)
    (x : X) (v : term k D M (n+1)) :
    (inr x : A) • suffixEmbed k D X N M s e (n+1) v =
      idealSuffixEmbed k D X N M s n e
        (BimoduleTensor.collapse k D X (term k D M n) (x ⊗ₜ[k] v)) := by
  induction v using TensorProduct.inductionOn with
  | tmul d v =>
    rw [suffixEmbed_tmul, BimoduleTensor.collapse_tmul, idealSuffixEmbed_tmul]
    change ((inr x : A) * inl d) ⊗ₜ[k] _ = (inr (MulOpposite.op d • x) : A) ⊗ₜ[k] _
    rw [inr_mul_inl]
  | add v w hv hw => simp only [map_add, smul_add, TensorProduct.tmul_add, hv, hw]

/-- General two-sided X-bar comparison. Both horizontal and signed suffix
faces are retained; the right D action is the bimodule's original action. -/
theorem parity_idealSuffixEmbed (s n : ℕ) (e : M →ₗ[k] term k A N (s+1))
    (he : ∀ (d : D) (v : M), e (d • v) = (inl d : A) • e v)
    (v : X ⊗[k] term k D M (n+1)) :
    SquareZero.multibarAugmentedDifferential k D X N (((s+1)+n)+1)
      (idealSuffixEmbed k D X N M (s+1) (n+1) e v) =
    -idealSuffixEmbed k D X N M (s+1) n e (BimoduleTensor.barDifferential k D X M n v) +
      (-1 : k)^(n+1) • termCast k D X N (show (s+(n+1))+1=((s+1)+n)+1 by omega)
        (idealSuffixEmbed k D X N M s (n+1)
          ((SquareZero.multibarAugmentedDifferential k D X N s).comp e) v) := by
  induction v using TensorProduct.inductionOn with
  | tmul x v =>
    rw [idealSuffixEmbed_tmul, SquareZero.multibarAugmentedDifferential_succ,
      SquareZero.slotParity_ideal, parity_suffixEmbed k D X N M s n e he,
      BimoduleTensor.barDifferential_tmul, map_sub, idealSuffixEmbed_tmul,
      idealSuffixEmbed_tmul, termCast_tmul k D X N (show s+(n+1)=(s+1)+n by omega)]
    have hn : (-inr x : A) • suffixEmbed k D X N M (s+1) e (n+1) v =
        -((inr x : A) • suffixEmbed k D X N M (s+1) e (n+1) v) :=
      _root_.neg_smul (inr x : A) (suffixEmbed k D X N M (s+1) e (n+1) v)
    rw [hn, ideal_action_suffixEmbed]
    erw [TensorProduct.neg_tmul, TensorProduct.tmul_add, TensorProduct.tmul_smul]
    abel
  | add v w hv hw => simp only [map_add, hv, hw, neg_add, smul_add]; abel

omit [Module D M] [IsScalarTower k D M] in
/-- At an empty D block the ideal endpoint vanishes, leaving all suffix faces. -/
theorem parity_idealSuffixEmbed_zero (s : ℕ) (e : M →ₗ[k] term k A N (s+1))
    (he : ∀ (x : X) (v : M), (inr x : A) • e v = 0)
    (v : X ⊗[k] M) :
    SquareZero.multibarAugmentedDifferential k D X N (s+1)
      (idealSuffixEmbed k D X N M (s+1) 0 e v) =
    idealSuffixEmbed k D X N M s 0
      ((SquareZero.multibarAugmentedDifferential k D X N s).comp e) v := by
  induction v using TensorProduct.inductionOn with
  | tmul x v =>
    rw [idealSuffixEmbed_tmul, SquareZero.multibarAugmentedDifferential_succ,
      SquareZero.slotParity_ideal]
    change (-inr x : A) • e v - (-inr x : A) ⊗ₜ[k] _ = (inr x : A) ⊗ₜ[k] _
    have hn : (-inr x : A) • e v = -((inr x : A) • e v) :=
      _root_.neg_smul (inr x : A) (e v)
    rw [hn, he, neg_zero, TensorProduct.neg_tmul, zero_sub, neg_neg]
    rfl
  | add v w hv hw => simp only [map_add, hv, hw]
end DerivedBar.ParityBridge

end

end OAI
