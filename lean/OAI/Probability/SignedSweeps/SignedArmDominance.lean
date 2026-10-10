import OAI.Probability.SignedSweeps.PairDominance
import OAI.Probability.SignedSweeps.MajorizationFactorial
import OAI.Probability.SignedSweeps.HookArms

namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct Classical
open Module

lemma pair_signed_row_prefix {u v n q : ℕ}
    (a : Partition u) (b : Partition v) (lam : Partition n)
    (hb : b.1.colLen 0 ≤ q) (e : Fin u ⊕ Fin v ≃ Fin n)
    (f : (Specht a ⊗[ℂ] Specht b.transpose) →ₗ[ℂ] Specht lam)
    (hf : Function.Injective f)
    (hint : ∀ (g : SymmetricGroup u) (h : SymmetricGroup v) x,
      f (TensorProduct.map (spechtRepresentation a g) (spechtRepresentation b.transpose h) x) =
        spechtRepresentation lam (e.permCongr (g.sumCongr h)) (f x)) (k : ℕ) :
    ∑ i ∈ Finset.range k, (lam.1.rowLen i - q) ≤ ∑ i ∈ Finset.range k, a.1.rowLen i := by
  have hh (j : ℕ) : ∑ i ∈ Finset.range j, lam.1.rowLen i ≤
      ∑ i ∈ Finset.range j, (a.1.rowLen i + q) := by
    have ht := pair_occurrence_topRowCount a b.transpose lam e f hf hint j
    simp only [topRowCount_eq_sum_rows, Partition.transpose, YoungDiagram.rowLen_transpose] at ht
    apply ht.trans
    rw [Finset.sum_add_distrib]
    exact Nat.add_le_add_left (Finset.sum_le_sum (fun i _ =>
      (b.1.colLen_anti 0 i (Nat.zero_le _)).trans hb)) _
  have ht := prefix_dominance_excess (fun i => lam.1.rowLen i)
    (fun i => a.1.rowLen i + q) k (fun i j h => lam.1.rowLen_anti i j h)
    (fun j _ => hh j) q
  simpa only [Nat.add_sub_cancel] using ht

lemma pair_signed_col_prefix {u v n q : ℕ}
    (a : Partition u) (b : Partition v) (lam : Partition n)
    (ha : a.1.colLen 0 ≤ q) (e : Fin u ⊕ Fin v ≃ Fin n)
    (f : (Specht a ⊗[ℂ] Specht b.transpose) →ₗ[ℂ] Specht lam)
    (hf : Function.Injective f)
    (hint : ∀ (g : SymmetricGroup u) (h : SymmetricGroup v) x,
      f (TensorProduct.map (spechtRepresentation a g) (spechtRepresentation b.transpose h) x) =
        spechtRepresentation lam (e.permCongr (g.sumCongr h)) (f x)) (k : ℕ) :
    ∑ j ∈ Finset.range k, (lam.1.colLen j - q) ≤ ∑ j ∈ Finset.range k, b.1.rowLen j := by
  have hh (j : ℕ) : ∑ i ∈ Finset.range j, lam.1.colLen i ≤
      ∑ i ∈ Finset.range j, (b.1.rowLen i + q) := by
    have ht := pair_occurrence_topColCount a b.transpose lam e f hf hint j
    simp only [topRowCount_eq_sum_rows, Partition.transpose,
      YoungDiagram.transpose_transpose, YoungDiagram.rowLen_transpose] at ht
    apply ht.trans
    rw [Finset.sum_add_distrib]
    simpa only [add_comm] using Nat.add_le_add_right
      (Finset.sum_le_sum (fun i _ => (a.1.colLen_anti 0 i (Nat.zero_le _)).trans ha))
      (∑ i ∈ Finset.range j, b.1.rowLen i)
  have ht := prefix_dominance_excess (fun i => lam.1.colLen i)
    (fun i => b.1.rowLen i + q) k (fun i j h => lam.1.colLen_anti i j h)
    (fun j _ => hh j) q
  simpa only [Nat.add_sub_cancel] using ht

lemma topRowCount_le_card (lam : YoungDiagram) (k : ℕ) : topRowCount lam k ≤ lam.card :=
  Finset.card_le_card (Finset.filter_subset _ _)

lemma topColCount_add_row_excess {n : ℕ} (lam : Partition n) (q : ℕ) :
    topRowCount lam.1.transpose q +
      (∑ i ∈ Finset.range (lam.1.colLen 0), (lam.1.rowLen i - q)) = n := by
  have ht : topRowCount lam.1.transpose q =
      ∑ i ∈ Finset.range (lam.1.colLen 0), min q (lam.1.rowLen i) := by
    rw [topRowCount_eq_sum_columns,
      Fin.sum_univ_eq_sum_range (fun j => min q (lam.1.transpose.colLen j)),
      YoungDiagram.rowLen_transpose]
    simp only [YoungDiagram.colLen_transpose]
  rw [ht, ← Finset.sum_add_distrib]
  have he (i : ℕ) : min q (lam.1.rowLen i) + (lam.1.rowLen i - q) = lam.1.rowLen i := by omega
  simp_rw [he]
  have hh := lam.sum_rowLen
  rw [Fin.sum_univ_eq_sum_range (fun i => lam.1.rowLen i)] at hh
  exact hh

lemma topRowCount_transpose_filter (lam : YoungDiagram) (q : ℕ) :
    topRowCount lam.transpose q = (lam.cells.filter (fun c => c.2 < q)).card := by
  unfold topRowCount
  rw [show lam.transpose.cells = lam.cells.map (Equiv.prodComm ℕ ℕ).toEmbedding from rfl,
    Finset.filter_map, Finset.card_map]
  rfl

lemma signedHook_of_cover (lam : YoungDiagram) (q : ℕ)
    (hcover : lam.card ≤ topRowCount lam q + topRowCount lam.transpose q) :
    IsSignedHook (2*q) lam := by
  let A := lam.cells.filter (fun c => c.1 < q)
  let B := lam.cells.filter (fun c => c.2 < q)
  let S := lam.cells \ (A ∪ B)
  have hsub : A ∪ B ⊆ lam.cells := Finset.union_subset
    (Finset.filter_subset _ _) (Finset.filter_subset _ _)
  have hAB : (A ∩ B).card ≤ q*q := by
    have hs : A ∩ B ⊆ Finset.range q ×ˢ Finset.range q := by
      intro c hc
      rcases Finset.mem_inter.mp hc with ⟨ha,hb⟩
      exact Finset.mem_product.mpr ⟨Finset.mem_range.mpr (Finset.mem_filter.mp ha).2,
        Finset.mem_range.mpr (Finset.mem_filter.mp hb).2⟩
    simpa using Finset.card_le_card hs
  have hScard : S.card ≤ q*q := by
    have ht := Finset.card_sdiff_add_card_eq_card hsub
    have hi := Finset.card_union_add_card_inter A B
    rw [topRowCount_transpose_filter] at hcover
    change lam.cells.card ≤ A.card + B.card at hcover
    dsimp only [S]
    omega
  unfold IsSignedHook
  by_contra hn
  have hm : (2*q,2*q) ∈ lam := YoungDiagram.mem_iff_lt_rowLen.mpr (Nat.lt_of_not_ge hn)
  let T := Finset.Icc q (2*q) ×ˢ Finset.Icc q (2*q)
  have hT : T ⊆ S := by
    intro c hc
    rcases Finset.mem_product.mp hc with ⟨hc₁,hc₂⟩
    rcases Finset.mem_Icc.mp hc₁ with ⟨h₁,h₂⟩
    rcases Finset.mem_Icc.mp hc₂ with ⟨h₃,h₄⟩
    apply Finset.mem_sdiff.mpr
    refine ⟨lam.isLowerSet (Prod.mk_le_mk.mpr ⟨h₂,h₄⟩) hm, ?_⟩
    simp only [A, B, Finset.mem_union, Finset.mem_filter, not_or]
    exact ⟨fun h => (Nat.not_lt.mpr h₁) h.2, fun h => (Nat.not_lt.mpr h₃) h.2⟩
  have ht := (Finset.card_le_card hT).trans hScard
  have htc : T.card = (q+1)*(q+1) := by
    simp only [T, Finset.card_product, Nat.card_Icc]
    congr 1 <;> omega
  rw [htc] at ht
  nlinarith

theorem pair_signed_hook {u v n q : ℕ}
    (hn : u+v=n) (a : Partition u) (b : Partition v) (lam : Partition n)
    (ha : a.1.colLen 0 ≤ q) (hb : b.1.colLen 0 ≤ q)
    (e : Fin u ⊕ Fin v ≃ Fin n)
    (f : (Specht a ⊗[ℂ] Specht b.transpose) →ₗ[ℂ] Specht lam)
    (hf : Function.Injective f)
    (hint : ∀ (g : SymmetricGroup u) (h : SymmetricGroup v) x,
      f (TensorProduct.map (spechtRepresentation a g) (spechtRepresentation b.transpose h) x) =
        spechtRepresentation lam (e.permCongr (g.sumCongr h)) (f x)) :
    IsSignedHook (2*q) lam.1 := by
  have hr := (pair_signed_row_prefix a b lam hb e f hf hint (lam.1.colLen 0)).trans
    (show ∑ i ∈ Finset.range (lam.1.colLen 0), a.1.rowLen i ≤ u by
      rw [← topRowCount_eq_sum_rows]; exact (topRowCount_le_card _ _).trans_eq a.2)
  have hc := (pair_signed_col_prefix a b lam ha e f hf hint (lam.1.rowLen 0)).trans
    (show ∑ i ∈ Finset.range (lam.1.rowLen 0), b.1.rowLen i ≤ v by
      rw [← topRowCount_eq_sum_rows]; exact (topRowCount_le_card _ _).trans_eq b.2)
  have heR := topColCount_add_row_excess lam q
  have heC := topColCount_add_row_excess lam.transpose q
  simp only [Partition.transpose, YoungDiagram.transpose_transpose,
    YoungDiagram.rowLen_transpose, YoungDiagram.colLen_transpose] at heC
  apply signedHook_of_cover
  rw [lam.2]
  omega

end SignedSweeps
end

end OAI
