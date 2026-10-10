import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.Normed.Group.Basic

namespace OAI

/-!
# Square summation of disjoint residual blocks

The finite deterministic estimates in §10 `res:block-square`: error
envelopes are summed in ℓ¹, main envelopes in ℓ², and each block contains
only a bounded number of lengths. Multiplicities of packets at one
length are already included in the corresponding envelope.
-/

noncomputable section

open scoped BigOperators

namespace LipschitzHilbert

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

theorem sum_disjoint_blocks_le (I : ι → Finset κ)
    (hI : Pairwise (fun i j => Disjoint (I i) (I j)))
    (e : κ → ℝ) (he : ∀ k, 0 ≤ e k) :
    (∑ i, ∑ k ∈ I i, e k) ≤ ∑ k, e k := by
  classical
  have hd : Set.PairwiseDisjoint (↑(Finset.univ : Finset ι)) I :=
    fun i _ j _ hij => hI hij
  rw [← Finset.sum_biUnion hd]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
    (fun k _ _ => he k)

theorem error_blocks_square_sum_le (I : ι → Finset κ)
    (hI : Pairwise (fun i j => Disjoint (I i) (I j)))
    (e : κ → ℝ) (he : ∀ k, 0 ≤ e k) :
    (∑ i, (∑ k ∈ I i, e k) ^ 2) ≤ (∑ k, e k) ^ 2 := by
  have hs := sum_disjoint_blocks_le I hI e he
  have hsmall : 0 ≤ ∑ i, ∑ k ∈ I i, e k :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun k _ => he k
  have hlarge : 0 ≤ ∑ k, e k := Finset.sum_nonneg fun k _ => he k
  refine (Finset.sum_sq_le_sq_sum_of_nonneg
    (fun i _ => Finset.sum_nonneg fun k _ => he k)).trans ?_
  nlinarith

theorem main_blocks_square_sum_le (I : ι → Finset κ)
    (hI : Pairwise (fun i j => Disjoint (I i) (I j)))
    (a : κ → ℝ) {L : ℝ} (hL : 0 ≤ L) (hcard : ∀ i, ((I i).card : ℝ) ≤ L) :
    (∑ i, (∑ k ∈ I i, a k) ^ 2) ≤ L * ∑ k, (a k) ^ 2 := by
  have hblock (i : ι) : (∑ k ∈ I i, a k) ^ 2 ≤ L * ∑ k ∈ I i, (a k) ^ 2 := by
    have h := Finset.sum_mul_sq_le_sq_mul_sq (I i) (fun _ => (1 : ℝ)) a
    simp only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one] at h
    exact h.trans (mul_le_mul_of_nonneg_right (hcard i) (Finset.sum_nonneg fun k _ => sq_nonneg (a k)))
  calc
    _ ≤ ∑ i, L * ∑ k ∈ I i, (a k) ^ 2 := Finset.sum_le_sum fun i _ => hblock i
    _ = L * ∑ i, ∑ k ∈ I i, (a k) ^ 2 := (Finset.mul_sum ..).symm
    _ ≤ L * ∑ k, (a k) ^ 2 := mul_le_mul_of_nonneg_left
      (sum_disjoint_blocks_le I hI (fun k => (a k) ^ 2) (fun k => sq_nonneg (a k))) hL

/-- A residual block is controlled by its error and main envelopes and
a final-block remainder. Their full square sum has no depth factor. -/
theorem residual_blocks_square_sum_le {E : Type*} [NormedAddCommGroup E]
    (I : ι → Finset κ) (hI : Pairwise (fun i j => Disjoint (I i) (I j)))
    (e a : κ → ℝ) (he : ∀ k, 0 ≤ e k) (ha : ∀ k, 0 ≤ a k)
    (B : ι → E) (r : ι → ℝ) (hr : ∀ i, 0 ≤ r i)
    {C L R : ℝ} (_hC : 0 ≤ C) (hL : 0 ≤ L) (hR : 0 ≤ R)
    (hcard : ∀ i, ((I i).card : ℝ) ≤ L) (hremainder : ∑ i, r i ≤ R)
    (hbound : ∀ i, ‖B i‖ ≤ C * ((∑ k ∈ I i, e k) + ∑ k ∈ I i, a k) + r i) :
    (∑ i, ‖B i‖ ^ 2) ≤
      3 * C ^ 2 * ((∑ k, e k) ^ 2 + L * ∑ k, (a k) ^ 2) + 3 * R ^ 2 := by
  have hpoint (i : ι) : ‖B i‖ ^ 2 ≤
      3 * C ^ 2 * ((∑ k ∈ I i, e k) ^ 2 + (∑ k ∈ I i, a k) ^ 2) + 3 * (r i) ^ 2 := by
    have he0 : 0 ≤ ∑ k ∈ I i, e k := Finset.sum_nonneg fun k _ => he k
    have ha0 : 0 ≤ ∑ k ∈ I i, a k := Finset.sum_nonneg fun k _ => ha k
    have hb0 := norm_nonneg (B i)
    have hb := hbound i
    have hs : ‖B i‖ ^ 2 ≤ (C * ((∑ k ∈ I i, e k) + ∑ k ∈ I i, a k) + r i) ^ 2 := by
      nlinarith [mul_nonneg _hC (add_nonneg he0 ha0), hr i]
    nlinarith [sq_nonneg (C * (∑ k ∈ I i, e k) - C * (∑ k ∈ I i, a k)),
      sq_nonneg (C * (∑ k ∈ I i, e k) - r i),
      sq_nonneg (C * (∑ k ∈ I i, a k) - r i)]
  have heBound := error_blocks_square_sum_le I hI e he
  have haBound := main_blocks_square_sum_le I hI a hL hcard
  have hrBound : (∑ i, (r i) ^ 2) ≤ R ^ 2 := by
    refine (Finset.sum_sq_le_sq_sum_of_nonneg (fun i _ => hr i)).trans ?_
    have hr0 : 0 ≤ ∑ i, r i := Finset.sum_nonneg fun i _ => hr i
    nlinarith
  calc
    _ ≤ ∑ i, (3 * C ^ 2 * ((∑ k ∈ I i, e k) ^ 2 + (∑ k ∈ I i, a k) ^ 2) + 3 * (r i) ^ 2) :=
      Finset.sum_le_sum fun i _ => hpoint i
    _ = 3 * C ^ 2 * ((∑ i, (∑ k ∈ I i, e k) ^ 2) +
        ∑ i, (∑ k ∈ I i, a k) ^ 2) + 3 * ∑ i, (r i) ^ 2 := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_add_distrib]
    _ ≤ _ := add_le_add
      (mul_le_mul_of_nonneg_left (add_le_add heBound haBound) (by positivity))
      (mul_le_mul_of_nonneg_left hrBound (by norm_num))

end LipschitzHilbert

end

end OAI
