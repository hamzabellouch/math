import OAI.Probability.SignedSweeps.WordEntropy
import OAI.Probability.SignedSweeps.SignedPairDimension

namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators Classical TensorProduct
open Module

lemma entropy_monomial_eq {I : Type*} [Fintype I] (a : I → ℕ)
    (ha : ∀ i, 0 < a i) {p : ℕ} (hp : 0 < p) :
    (∏ i, ((a i : ℝ) / p) ^ a i) =
      Real.exp (-(∑ i, (a i : ℝ) * Real.log ((p : ℝ) / a i))) := by
  rw [← Finset.sum_neg_distrib, Real.exp_sum]
  apply Finset.prod_congr rfl
  intro i _
  have he : -((a i : ℝ) * Real.log ((p : ℝ) / a i)) =
      (a i : ℝ) * Real.log ((a i : ℝ) / p) := by
    rw [Real.log_div (Nat.cast_pos.mpr hp).ne' (Nat.cast_pos.mpr (ha i)).ne',
      Real.log_div (Nat.cast_pos.mpr (ha i)).ne' (Nat.cast_pos.mpr hp).ne']
    ring
  rw [he, Real.exp_nat_mul, Real.exp_log (div_pos (Nat.cast_pos.mpr (ha i)) (Nat.cast_pos.mpr hp))]

def normalizedRowColors {u : ℕ} (α : Partition u) (q p : ℕ) : Fin q → ℝ :=
  fun i => (α.1.rowLen i : ℝ) / p

lemma normalizedRowColors_nonneg {u : ℕ} (α : Partition u) (q p : ℕ) (i : Fin q) :
    0 ≤ normalizedRowColors α q p i := by
  unfold normalizedRowColors
  positivity

lemma normalizedRowColors_sum {u q p : ℕ} (α : Partition u)
    (hα : α.1.colLen 0 ≤ q) :
    ∑ i, normalizedRowColors α q p i = (u : ℝ) / p := by
  unfold normalizedRowColors
  rw [← Finset.sum_div,
    Fin.sum_univ_eq_sum_range (fun i => (α.1.rowLen i : ℝ))]
  congr 1
  exact_mod_cast rowLen_sum_range α hα

lemma normalizedPairColors_sum {u v p q : ℕ} (h : u+v=p) (hp : 0 < p)
    (α : Partition u) (β : Partition v)
    (hα : α.1.colLen 0 ≤ q) (hβ : β.1.colLen 0 ≤ q) :
    (∑ i, normalizedRowColors α q p i) + (∑ i, normalizedRowColors β q p i) = 1 := by
  rw [normalizedRowColors_sum α hα, normalizedRowColors_sum β hβ, ← add_div]
  have he : (u : ℝ) + v = p := by exact_mod_cast h
  rw [he, div_self (Nat.cast_pos.mpr hp).ne']

lemma normalizedPairColors_monomial {u v p q : ℕ} (h : u+v=p) (hp : 0 < p)
    (α : Partition u) (β : Partition v)
    (hα : α.1.colLen 0 ≤ q) (hβ : β.1.colLen 0 ≤ q) :
    (∏ i, normalizedRowColors α q p (Fin.castLE hα (α.rowIndex i))) *
      (∏ i, normalizedRowColors β q p (Fin.castLE hβ (β.rowIndex i))) =
        Real.exp (-signedEntropy α β) := by
  let e : Fin (α.1.colLen 0) ↪ Fin q := ⟨Fin.castLE hα, Fin.castLE_injective _⟩
  let f : Fin (β.1.colLen 0) ↪ Fin q := ⟨Fin.castLE hβ, Fin.castLE_injective _⟩
  change (∏ i, normalizedRowColors α q p (rowColorWord α e i)) *
    (∏ i, normalizedRowColors β q p (rowColorWord β f i)) = _
  rw [rowColor_monomial_eq, rowColor_monomial_eq]
  have he : signedEntropy α β =
      ∑ i : Fin (α.1.colLen 0) ⊕ Fin (β.1.colLen 0),
        ((Sum.elim (fun j : Fin (α.1.colLen 0) => α.1.rowLen j)
            (fun j : Fin (β.1.colLen 0) => β.1.rowLen j) i : ℕ) : ℝ) *
          Real.log ((p : ℝ) / (Sum.elim (fun j : Fin (α.1.colLen 0) => α.1.rowLen j)
            (fun j : Fin (β.1.colLen 0) => β.1.rowLen j) i)) := by
    have hn : (u : ℝ)+v = p := by exact_mod_cast h
    simp only [signedEntropy, List.map_append, List.sum_append,
      Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, hn]
    exact congrArg₂ (· + ·) (partsEntropy_rowLen α _) (partsEntropy_rowLen β _)
  rw [he]
  have hh := entropy_monomial_eq
    (Sum.elim (fun i : Fin (α.1.colLen 0) => α.1.rowLen i)
      (fun i : Fin (β.1.colLen 0) => β.1.rowLen i))
    (by intro i; cases i with | inl i => exact α.rowLen_pos i | inr i => exact β.rowLen_pos i) hp
  simpa only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr,
    normalizedRowColors, e, f, Function.Embedding.coeFn_mk, Fin.val_castLE] using hh

end SignedSweeps
end

end OAI
