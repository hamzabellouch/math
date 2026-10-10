import Mathlib
import OAI.Geometry.HyperbolicGroups.BFSLevels
import OAI.Geometry.HyperbolicGroups.ConnectedLevels

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction.PlanarRecursion
open SimpleGraph
attribute [local instance] Classical.propDecidable
variable {V : Type*} [DecidableEq V]

/-- Truncate a root-path separator between two sparse BFS levels.  No
contraction, new embedding, or connectedness of the specified set is needed. -/
theorem annular_separator (G : SimpleGraph V) (U B : Finset V) (depth : V → ℤ)
    (hd : ∀ v w, G.Adj v w → depth v ≤ depth w+1 ∧ depth w ≤ depth v+1)
    (m L H : ℤ) (hLm : L ≤ m) (hmH : m ≤ H)
    (hbelow : 2*(U.filter (fun v => depth v < m)).card ≤ U.card)
    (habove : 2*(U.filter (fun v => m < depth v)).card ≤ U.card)
    (hB : ∀ W : Finset V, W ⊆ U → Disjoint W B →
      (G.induce (W : Set V)).Preconnected → 2*W.card ≤ U.card) :
    ∃ S : Finset V, S ⊆ U ∧
      S.card ≤ (U.filter (fun v => depth v = L)).card +
        (U.filter (fun v => depth v = H)).card +
        (B.filter (fun v => L ≤ depth v ∧ depth v ≤ H)).card ∧
      ∀ W : Finset V, W ⊆ U → Disjoint W S →
        (G.induce (W : Set V)).Preconnected → 2*W.card ≤ U.card := by
  classical
  let A := U.filter (fun v => depth v = L)
  let C := U.filter (fun v => depth v = H)
  let I := B.filter (fun v => L ≤ depth v ∧ depth v ≤ H)
  let S := (A ∪ C) ∪ (U ∩ I)
  have hSU : S ⊆ U := by
    intro v hv
    rcases Finset.mem_union.mp hv with hv | hv
    · rcases Finset.mem_union.mp hv with hv | hv
      · exact (Finset.mem_filter.mp hv).1
      · exact (Finset.mem_filter.mp hv).1
    · exact (Finset.mem_inter.mp hv).1
  refine ⟨S,hSU,?_,?_⟩
  · calc
      S.card ≤ (A ∪ C).card + (U ∩ I).card := Finset.card_union_le _ _
      _ ≤ A.card+C.card+I.card := Nat.add_le_add (Finset.card_union_le _ _) (Finset.card_le_card Finset.inter_subset_right)
  · intro W hWU hWS hc
    have hWL : ∀ v ∈ (W : Set V), depth v ≠ L := by
      intro v hv he
      apply Finset.disjoint_left.mp hWS hv
      exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hWU hv,he⟩))
    have hWH : ∀ v ∈ (W : Set V), depth v ≠ H := by
      intro v hv he
      apply Finset.disjoint_left.mp hWS hv
      exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hWU hv,he⟩))
    have hcl := connected_avoids_level G depth hd (W : Set V) hc L hWL
    have hch := connected_avoids_level G depth hd (W : Set V) hc H hWH
    by_cases he : W.Nonempty
    · obtain ⟨v,hv⟩ := he
      by_cases hvl : depth v < L
      · have hsub : W ⊆ U.filter (fun w => depth w < m) := by
          intro w hw
          have hwl := (hcl v hv w hw).mp hvl
          exact Finset.mem_filter.mpr ⟨hWU hw,lt_of_lt_of_le hwl hLm⟩
        exact (Nat.mul_le_mul_left 2 (Finset.card_le_card hsub)).trans hbelow
      · by_cases hvh : H < depth v
        · have hsub : W ⊆ U.filter (fun w => m < depth w) := by
            intro w hw
            have hwne := hWH w hw
            have hiff := hch v hv w hw
            exact Finset.mem_filter.mpr ⟨hWU hw,by omega⟩
          exact (Nat.mul_le_mul_left 2 (Finset.card_le_card hsub)).trans habove
        · apply hB W hWU _ hc
          apply Finset.disjoint_left.mpr
          intro w hw hwB
          have hwL := hWL w hw
          have hwH := hWH w hw
          have hvL := hWL v hv
          have hvH := hWH v hv
          have hliff := hcl v hv w hw
          have hhiff := hch v hv w hw
          have hband : L ≤ depth w ∧ depth w ≤ H := by omega
          apply Finset.disjoint_left.mp hWS hw
          exact Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨hWU hw,
            Finset.mem_filter.mpr ⟨hwB,hband⟩⟩)
    · rw [Finset.not_nonempty_iff_eq_empty.mp he]
      simp

/-- Uniform sqrt-cardinality bound from one balanced root-path hull; the
hull may be arbitrarily large, provided each integer depth strip has k
vertices per level. -/
theorem sqrt_separator_of_banded_hull (G : SimpleGraph V) (U B : Finset V)
    (depth : V → ℕ) (k : ℕ)
    (hd : ∀ v w, G.Adj v w → (depth v : ℤ) ≤ (depth w : ℤ)+1 ∧
      (depth w : ℤ) ≤ (depth v : ℤ)+1)
    (hband : ∀ L H : ℤ, (B.filter (fun v => L ≤ (depth v : ℤ) ∧ (depth v : ℤ) ≤ H)).card ≤
      k*(H-L+1).toNat)
    (hB : ∀ W : Finset V, W ⊆ U → Disjoint W B →
      (G.induce (W : Set V)).Preconnected → 2*W.card ≤ U.card) :
    ∃ S : Finset V, S ⊆ U ∧ S.card ≤ (3*k+2)*Nat.sqrt U.card ∧
      ∀ W : Finset V, W ⊆ U → Disjoint W S →
        (G.induce (W : Set V)).Preconnected → 2*W.card ≤ U.card := by
  classical
  by_cases hU : U = ∅
  · subst U
    refine ⟨∅,Finset.Subset.refl _,by simp,?_⟩
    intro W hW _ _
    have : W = ∅ := Finset.subset_empty.mp hW
    simp [this]
  let a := Nat.sqrt U.card
  obtain ⟨m,hml,hmh⟩ := median_level U depth
  obtain ⟨L,H,hLm,hmH,hwidth,hLc,hHc⟩ := two_sparse_levels U (fun v => (depth v : ℤ)) m a
  have hml' : 2*(U.filter (fun v => (depth v : ℤ) < (m : ℤ))).card ≤ U.card := by
    simpa only [Nat.cast_lt] using hml
  have hmh' : 2*(U.filter (fun v => (m : ℤ) < (depth v : ℤ))).card ≤ U.card := by
    simpa only [Nat.cast_lt] using hmh
  obtain ⟨S,hSU,hSc,hsep⟩ := annular_separator G U B (fun v => (depth v : ℤ)) hd m L H hLm hmH hml' hmh' hB
  refine ⟨S,hSU,?_,hsep⟩
  have hroot : U.card < (a+1)*(a+1) := Nat.lt_succ_sqrt U.card
  have hLsmall : (U.filter (fun v => (depth v : ℤ) = L)).card ≤ a := by nlinarith
  have hHsmall : (U.filter (fun v => (depth v : ℤ) = H)).card ≤ a := by nlinarith
  have ha : 1 ≤ a := Nat.sqrt_pos.mpr (Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hU))
  have hwidth' : (H-L+1).toNat ≤ 2*a+1 := by omega
  have hh := (hband L H).trans (Nat.mul_le_mul_left k hwidth')
  nlinarith

end HyperbolicObstruction.PlanarRecursion
end
end

section

end
end

end OAI
