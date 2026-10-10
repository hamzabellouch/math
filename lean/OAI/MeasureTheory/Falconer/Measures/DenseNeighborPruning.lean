import OAI.MeasureTheory.Falconer.Graphs.BipartitePivot

namespace OAI

/-! Removing the few vertices with many bad partners leaves many common
good partners for every retained pair. This is the path-counting part of
the additive-energy refinement. -/
namespace Falconer
attribute [local instance] Classical.propDecidable

theorem dense_neighbor_pruning (N : Finset ℤ) (bad : ℤ → ℤ → Prop)
    {u : ℝ} (hu : 0 < u) (hN : u/2 ≤ (N.card : ℝ))
    (hsum : (∑ b ∈ N, ((N.filter fun c => bad b c).card : ℝ)) ≤ u*(N.card : ℝ)/16) :
    ∃ G ⊆ N, (N.card : ℝ)/2 ≤ (G.card : ℝ) ∧
      ∀ b ∈ G, ∀ c ∈ G,
        (N.card : ℝ)/2 ≤ ((N.filter fun v => ¬bad b v ∧ ¬bad c v).card : ℝ) := by
  let w := fun b => ((N.filter fun c => bad b c).card : ℝ)
  let G := N.filter fun b => w b ≤ u/8
  let D := N.filter fun b => ¬w b ≤ u/8
  have hD : (u/8)*(D.card : ℝ) ≤ ∑ b ∈ N, w b := by
    calc
      _ = ∑ _b ∈ D, u/8 := by simp [mul_comm]
      _ ≤ ∑ b ∈ D, w b := Finset.sum_le_sum fun b hb =>
        (lt_of_not_ge (Finset.mem_filter.mp hb).2).le
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun _ _ _ => Nat.cast_nonneg _)
  have hsplit : (G.card : ℝ)+(D.card : ℝ) = N.card := by
    exact_mod_cast Finset.card_filter_add_card_filter_not (s := N) (fun b => w b ≤ u/8)
  have hGcard : (N.card : ℝ)/2 ≤ G.card := by
    change (∑ b ∈ N, w b) ≤ _ at hsum
    nlinarith
  refine ⟨G,Finset.filter_subset _ _,hGcard,?_⟩
  intro b hb c hc
  have hb' := (Finset.mem_filter.mp hb).2
  have hc' := (Finset.mem_filter.mp hc).2
  let H := N.filter fun v => ¬bad b v ∧ ¬bad c v
  let Db := N.filter fun v => bad b v
  let Dc := N.filter fun v => bad c v
  have hcover : N ⊆ H ∪ Db ∪ Dc := by
    intro v hv
    by_cases hbv : bad b v
    · exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hv,hbv⟩))
    · by_cases hcv : bad c v
      · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hv,hcv⟩)
      · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hv,hbv,hcv⟩))
  have hcard : (N.card : ℝ) ≤ (H.card : ℝ)+(Db.card : ℝ)+(Dc.card : ℝ) := by
    have h1 := Finset.card_le_card hcover
    have h2 := Finset.card_union_le (H ∪ Db) Dc
    have h3 := Finset.card_union_le H Db
    exact_mod_cast (show N.card ≤ H.card+Db.card+Dc.card by omega)
  have hDb : (Db.card : ℝ) ≤ u/8 := hb'
  have hDc : (Dc.card : ℝ) ≤ u/8 := hc'
  change (N.card : ℝ)/2 ≤ H.card
  linarith

theorem integer_bad_pair_rows (A B : Finset ℤ) (e : ℤ → ℤ → Prop) (L : ℝ) (a : ℤ) :
    (∑ b ∈ integerNeighbors B e a,
      (((integerNeighbors B e a).filter fun c => ((integerCommonNeighbors A e b c).card : ℝ) < L).card : ℝ)) =
      ((integerBadPairsAt A B e L a).card : ℝ) := by
  let N := integerNeighbors B e a
  have he : integerBadPairsAt A B e L a =
      (N ×ˢ N).filter fun p => ((integerCommonNeighbors A e p.1 p.2).card : ℝ) < L := by
    ext ⟨b,c⟩
    simp only [integerBadPairsAt,integerBadPairs,integerNeighbors,N,Finset.mem_filter,Finset.mem_product]
    tauto
  rw [he]
  have hn : (∑ b ∈ N, (N.filter fun c => ((integerCommonNeighbors A e b c).card : ℝ) < L).card) =
      ((N ×ˢ N).filter fun p => ((integerCommonNeighbors A e p.1 p.2).card : ℝ) < L).card := by
    simp only [Finset.card_eq_sum_ones,Finset.sum_filter,Finset.sum_product]
  exact_mod_cast hn

theorem integer_dense_good_partners (A B : Finset ℤ) (e : ℤ → ℤ → Prop)
    (hA : A.Nonempty) (hB : B.Nonempty) {ρ L : ℝ} (hρ : 0 < ρ) (hL : 0 ≤ L)
    (hsmall : L ≤ ρ^2*(A.card : ℝ)/32)
    (hdense : ρ*(A.card : ℝ)*(B.card : ℝ) ≤
      ∑ a ∈ A, ((integerNeighbors B e a).card : ℝ)) :
    ∃ a ∈ A, ∃ G ⊆ integerNeighbors B e a,
      ρ*(B.card : ℝ)/4 ≤ (G.card : ℝ) ∧
      ∀ b ∈ G, ∀ c ∈ G,
        ρ*(B.card : ℝ)/4 ≤ (((integerNeighbors B e a).filter fun v =>
          L ≤ (integerCommonNeighbors A e b v).card ∧
          L ≤ (integerCommonNeighbors A e c v).card).card : ℝ) := by
  obtain ⟨a,ha,hN,hbad⟩ := integer_dense_pivot A B e hA hB hρ hL hsmall hdense
  have hsum : (∑ b ∈ integerNeighbors B e a,
      (((integerNeighbors B e a).filter fun c => ((integerCommonNeighbors A e b c).card : ℝ) < L).card : ℝ)) ≤
      (ρ*(B.card : ℝ))*(integerNeighbors B e a).card/16 := by
    rw [integer_bad_pair_rows]
    linarith
  obtain ⟨G,hGN,hGcard,hpartners⟩ := dense_neighbor_pruning (integerNeighbors B e a)
    (fun b c => ((integerCommonNeighbors A e b c).card : ℝ) < L)
    (by have hb : (0 : ℝ) < B.card := Nat.cast_pos.mpr (Finset.card_pos.mpr hB); positivity) hN hsum
  refine ⟨a,ha,G,hGN,by linarith,?_⟩
  intro b hb c hc
  have hp := hpartners b hb c hc
  simp only [not_lt] at hp
  exact (show ρ*(B.card : ℝ)/4 ≤ (integerNeighbors B e a).card/2 by linarith).trans hp

end Falconer

end OAI
