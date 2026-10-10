import Mathlib
import OAI.Combinatorics.BinaryEdit.MatchingSublist
import OAI.Combinatorics.TreeEdit.Alignments

namespace OAI

/-! Ordered equal-label bit matches can be colored by their ordinal modulo
block width. This avoids the bipartite edge-coloring theorem in the source. -/

namespace TreeEdit.BinaryLower.Code

/-- If every increasing block matching has at most `L` edges, then an increasing
bit matching whose edges all join equal original labels has at most `P * L`
edges. The hypothesis on each finite subset is precisely the longest-common-
subsequence bound after the two block maps become strictly increasing. -/
theorem equal_match_count_le {N P L : ℕ} (hP : 0 < P)
    (f g : Fin N → ℕ) (hf : StrictMono f) (hg : StrictMono g)
    (hL : ∀ s : Finset (Fin N),
      StrictMonoOn (fun i => f i / P) (s : Set (Fin N)) →
      StrictMonoOn (fun i => g i / P) (s : Set (Fin N)) → s.card ≤ L) :
    N ≤ P * L := by
  classical
  have bound := Finset.card_le_mul_card_image_of_maps_to
    (s := Finset.univ) (t := Finset.range P) (f := fun i : Fin N => i.val % P)
    (fun i _ => Finset.mem_range.mpr (Nat.mod_lt i.val hP)) L
    (by
      intro r hr
      apply hL
      · intro i hi j hj hij
        exact div_strict_of_equal_residue hP f hf hij
          ((Finset.mem_filter.mp hi).2.trans (Finset.mem_filter.mp hj).2.symm)
      · intro i hi j hj hij
        exact div_strict_of_equal_residue hP g hg hij
          ((Finset.mem_filter.mp hi).2.trans (Finset.mem_filter.mp hj).2.symm))
  simpa [Nat.mul_comm] using bound

/-- Concrete equal-label case of the modular coloring estimate. The strictly
increasing lists `f,g` are the bit positions of the equal-label matches; their
quotients index the original words. -/
theorem equal_label_match_count_le {α : Type*} {N P : ℕ} (hP : 0 < P)
    (x y : List α) (f g : Fin N → ℕ) (hf : StrictMono f) (hg : StrictMono g)
    (hfx : ∀ i, f i / P < x.length) (hgy : ∀ i, g i / P < y.length)
    (heq : ∀ i, x.get ⟨f i / P, hfx i⟩ = y.get ⟨g i / P, hgy i⟩) :
    N ≤ P * lcs x y := by
  apply equal_match_count_le hP f g hf hg
  intro s hs₁ hs₂
  let e := s.orderEmbOfFin rfl
  let f' : Fin s.card → Fin x.length := fun i => ⟨f (e i) / P, hfx (e i)⟩
  let g' : Fin s.card → Fin y.length := fun i => ⟨g (e i) / P, hgy (e i)⟩
  have hf' : StrictMono f' := by
    intro i j hij
    exact hs₁ (s.orderEmbOfFin_mem rfl i) (s.orderEmbOfFin_mem rfl j)
      (e.strictMono hij)
  have hg' : StrictMono g' := by
    intro i j hij
    exact hs₂ (s.orderEmbOfFin_mem rfl i) (s.orderEmbOfFin_mem rfl j)
      (e.strictMono hij)
  exact matching_length_le_lcs x y f' g' hf' hg' (fun i => heq (e i))

/-- The same estimate for a selected subset of a larger increasing bit matching.
This is convenient when selecting exactly the equal-label edges. -/
theorem equal_label_subset_card_le {α : Type*} {N P : ℕ} (hP : 0 < P)
    (x y : List α) (f g : Fin N → ℕ) (hf : StrictMono f) (hg : StrictMono g)
    (hfx : ∀ i, f i / P < x.length) (hgy : ∀ i, g i / P < y.length)
    (s : Finset (Fin N))
    (heq : ∀ i ∈ s, x.get ⟨f i / P, hfx i⟩ = y.get ⟨g i / P, hgy i⟩) :
    s.card ≤ P * lcs x y := by
  let e := s.orderEmbOfFin rfl
  exact equal_label_match_count_le hP x y (f ∘ e) (g ∘ e)
    (hf.comp e.strictMono) (hg.comp e.strictMono)
    (fun i => hfx (e i)) (fun i => hgy (e i))
    (fun i => heq (e i) (s.orderEmbOfFin_mem rfl i))

end TreeEdit.BinaryLower.Code

end OAI
