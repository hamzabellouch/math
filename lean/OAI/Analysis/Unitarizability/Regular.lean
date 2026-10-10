import OAI.Analysis.Unitarizability.SparseSplitting
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Data.Fintype.Card

namespace OAI

/-! Regular convolution operators, product lists with multiplicity,
and sparse splitting from a contracting average. -/
noncomputable section
namespace Dixmier
universe u
open Finset
attribute [local instance] Classical.propDecidable

variable {G : Type*}

def reindexL2 (e : G ≃ G) (ξ : ScalarL2 G) : ScalarL2 G :=
  ⟨fun x => ξ (e x), memℓp_gen (((lp.memℓp ξ).summable (by norm_num)).comp_injective e.injective)⟩

@[simp] theorem reindexL2_apply (e : G ≃ G) (ξ : ScalarL2 G) (x : G) :
    reindexL2 e ξ x = ξ (e x) := rfl

theorem l2_norm_sq (ξ : ScalarL2 G) : ‖ξ‖ ^ 2 = ∑' x, ‖ξ x‖ ^ 2 := by
  simpa using lp.norm_rpow_eq_tsum (p := 2) (by norm_num) ξ

theorem reindexL2_norm (e : G ≃ G) (ξ : ScalarL2 G) : ‖reindexL2 e ξ‖ = ‖ξ‖ := by
  have hs : ‖reindexL2 e ξ‖ ^ 2 = ‖ξ‖ ^ 2 := by
    rw [l2_norm_sq, l2_norm_sq]
    exact e.tsum_eq (fun x => ‖ξ x‖ ^ 2)
  nlinarith [norm_nonneg (reindexL2 e ξ), norm_nonneg ξ]

def reindexIsometry (e : G ≃ G) : ScalarL2 G →ₗᵢ[ℂ] ScalarL2 G where
  toFun := reindexL2 e
  map_add' ξ η := by ext x; rfl
  map_smul' z ξ := by ext x; rfl
  norm_map' := reindexL2_norm e

variable [Group G]

/-- The right regular representation R_t ξ(x)=ξ(xt). -/
def rightRegular : G →* (ScalarL2 G →L[ℂ] ScalarL2 G) where
  toFun t := (reindexIsometry (Equiv.mulRight t)).toContinuousLinearMap
  map_one' := by ext ξ x; simp [reindexIsometry, reindexL2]
  map_mul' s t := by ext ξ x; simp [reindexIsometry, reindexL2, mul_assoc]

@[simp] theorem rightRegular_apply (t : G) (ξ : ScalarL2 G) (x : G) :
    rightRegular t ξ x = ξ (x * t) := rfl

theorem rightRegular_norm_map (t : G) (ξ : ScalarL2 G) : ‖rightRegular t ξ‖ = ‖ξ‖ :=
  reindexL2_norm (Equiv.mulRight t) ξ

/-- Left regular operators U_g commute with the right regular operators. -/
def leftRegular : G →* (ScalarL2 G →L[ℂ] ScalarL2 G) where
  toFun g := (reindexIsometry (Equiv.mulLeft g⁻¹)).toContinuousLinearMap
  map_one' := by ext ξ x; simp [reindexIsometry, reindexL2]
  map_mul' g h := by ext ξ x; simp [reindexIsometry, reindexL2]

@[simp] theorem leftRegular_apply (g : G) (ξ : ScalarL2 G) (x : G) :
    leftRegular g ξ x = ξ (g⁻¹ * x) := rfl

theorem left_right_commute (g t : G) : Commute (leftRegular g) (rightRegular t) := by
  change leftRegular g * rightRegular t = rightRegular t * leftRegular g
  ext ξ x
  simp [mul_assoc]

def Word (I : Type u) : ℕ → Type u
  | 0 => PUnit
  | n + 1 => I × Word I n

instance wordFintype {I : Type*} [Fintype I] : (n : ℕ) → Fintype (Word I n)
  | 0 => inferInstanceAs (Fintype PUnit)
  | n + 1 => by
    letI : Fintype (Word I n) := wordFintype n
    exact inferInstanceAs (Fintype (I × Word I n))

def wordProduct {I : Type*} (s : I → G) : (n : ℕ) → Word I n → G
  | 0, _ => 1
  | n + 1, w => s w.1 * wordProduct s n w.2

theorem word_card {I : Type*} [Fintype I] (n : ℕ) :
    Fintype.card (Word I n) = (Fintype.card I) ^ n := by
  induction n with
  | zero =>
    change Fintype.card PUnit = 1
    exact Fintype.card_unique
  | succ n ih =>
    change Fintype.card (I × Word I n) = _
    rw [Fintype.card_prod, ih, pow_succ']

/-- Product lists are indexed by words, not by their possibly colliding values. -/
theorem sum_wordProduct {I R : Type*} [Fintype I] [Semiring R]
    (s : I → G) (φ : G →* R) (n : ℕ) :
    (∑ w : Word I n, φ (wordProduct s n w)) = (∑ i, φ (s i)) ^ n := by
  induction n with
  | zero =>
    change (∑ w : PUnit, φ (1 : G)) = _
    simp
  | succ n ih =>
    change (∑ w : I × Word I n, φ (s w.1 * wordProduct s n w.2)) = _
    simp only [Fintype.sum_prod_type, map_mul, ← Finset.mul_sum, ← Finset.sum_mul, ih,
      pow_succ']

/-- Sparse splitting for words from a norm bound on the finite average. -/
theorem sparse_mask_for_words {I : Type*} [Fintype I] (s : I → G)
    {ρ : ℝ} (_hρ : 0 ≤ ρ)
    (havg : ‖∑ i, rightRegular (s i)‖ ≤ (Fintype.card I : ℝ) * ρ) (ℓ : ℕ) (hℓ : 0 < ℓ) :
    ∃ a : G → Word I ℓ → Bool,
      (∀ x, (rowOnes a x).card ≤ ⌈(Fintype.card I : ℝ) ^ ℓ * ρ ^ ℓ⌉₊) ∧
      ∀ y, (columnZeros a (wordProduct s ℓ) y).card ≤
        ⌈(Fintype.card I : ℝ) ^ ℓ * ρ ^ ℓ⌉₊ := by
  let A : ScalarL2 G →L[ℂ] ScalarL2 G := ∑ w : Word I ℓ, rightRegular (wordProduct s ℓ w)
  have hA : ∀ (ξ : ScalarL2 G) (x : G), A ξ x = ∑ w, ξ (x * wordProduct s ℓ w) := by
    intro ξ x
    simp only [A, _root_.sum_apply]
    rw [lp.coeFn_sum]
    simp only [Finset.sum_apply, rightRegular_apply]
  apply sparse_mask_of_convolution_bound (wordProduct s ℓ) A hA
  calc
    ‖A‖ = ‖(∑ i, rightRegular (s i)) ^ ℓ‖ := by
      dsimp only [A]
      rw [sum_wordProduct]
    _ ≤ ‖∑ i, rightRegular (s i)‖ ^ ℓ := norm_pow_le' _ hℓ
    _ ≤ ((Fintype.card I : ℝ) * ρ) ^ ℓ := pow_le_pow_left₀ (norm_nonneg _) havg ℓ
    _ = (Fintype.card I : ℝ) ^ ℓ * ρ ^ ℓ := mul_pow _ _ _
    _ ≤ ⌈(Fintype.card I : ℝ) ^ ℓ * ρ ^ ℓ⌉₊ := Nat.le_ceil _

end Dixmier

end

end OAI
