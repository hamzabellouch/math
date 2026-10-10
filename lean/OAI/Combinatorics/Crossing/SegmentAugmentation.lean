import OAI.Combinatorics.Crossing.EmbeddedGraphPaths
import OAI.Combinatorics.Crossing.DrawingSubdivisionGraph

namespace OAI

noncomputable section
namespace Zarankiewicz

theorem segment_endpoint_or_open (a b x : Plane) (hx : x ∈ segment ℝ a b) :
    x=a ∨ x=b ∨ x ∈ openSegmentTrace a b := by
  rw [← Path.range_segment] at hx
  obtain ⟨t,ht⟩ := hx
  by_cases ht0 : t=0
  · subst t
    exact Or.inl (by simpa only [Path.source] using ht.symm)
  by_cases ht1 : t=1
  · subst t
    exact Or.inr (Or.inl (by simpa only [Path.target] using ht.symm))
  refine Or.inr (Or.inr ⟨t.val,⟨?_,?_⟩,?_⟩)
  · exact lt_of_le_of_ne t.property.1 (fun he => ht0 (Subtype.ext he.symm))
  · exact lt_of_le_of_ne t.property.2 (fun he => ht1 (Subtype.ext he))
  · simpa only [Path.segment_apply,AffineMap.lineMap_apply_module,segmentPoint] using ht

def segmentAugmentedGraph {ι : Type*} (G : SimpleGraph Plane) (a b : ι → Plane)
    (hne : ∀ i, a i ≠ b i) : SimpleGraph Plane where
  Adj := fun x y => G.Adj x y ∨ ∃ i, (x=a i ∧ y=b i) ∨ (x=b i ∧ y=a i)
  symm := ⟨by
    rintro x y (hxy | ⟨i,⟨hx,hy⟩ | ⟨hx,hy⟩⟩)
    · exact Or.inl hxy.symm
    · exact Or.inr ⟨i,Or.inr ⟨hy,hx⟩⟩
    · exact Or.inr ⟨i,Or.inl ⟨hy,hx⟩⟩⟩
  loopless := ⟨by
    rintro x (hxx | ⟨i,⟨hx,hy⟩ | ⟨hx,hy⟩⟩)
    · exact G.loopless.irrefl x hxx
    · exact hne i (hx.symm.trans hy)
    · exact hne i (hy.symm.trans hx)⟩

theorem le_segmentAugmentedGraph {ι : Type*} (G : SimpleGraph Plane) (a b : ι → Plane)
    (hne : ∀ i, a i ≠ b i) : G ≤ segmentAugmentedGraph G a b hne := fun _ _ h => Or.inl h

theorem segmentAugmentedGraph_added_adj {ι : Type*} (G : SimpleGraph Plane) (a b : ι → Plane)
    (hne : ∀ i, a i ≠ b i) (i : ι) : (segmentAugmentedGraph G a b hne).Adj (a i) (b i) :=
  Or.inr ⟨i,Or.inl ⟨rfl,rfl⟩⟩

theorem exterior_segment_chord_meeting (G : SimpleGraph Plane) (U : Set Plane) (a b x y z : Plane)
    (hxy : G.Adj x y) (hout : ∀ x y, G.Adj x y → Disjoint (segment ℝ x y) U)
    (hin : openSegmentTrace a b ⊆ U)
    (ha : a ∈ segment ℝ x y → a=x ∨ a=y) (hb : b ∈ segment ℝ x y → b=x ∨ b=y)
    (hz : z ∈ segment ℝ x y) (hchord : z ∈ segment ℝ a b) :
    (z=x ∨ z=y) ∧ (z=a ∨ z=b) := by
  rcases segment_endpoint_or_open a b z hchord with rfl | rfl | hz'
  · exact ⟨ha hz,Or.inl rfl⟩
  · exact ⟨hb hz,Or.inr rfl⟩
  · exact False.elim (Set.disjoint_left.mp (hout x y hxy) hz (hin hz'))

theorem segmentAugmentedGraph_embedding {ι : Type*} (G : SimpleGraph Plane) (a b : ι → Plane)
    (hne : ∀ i, a i ≠ b i) (hemb : StraightEdgeEmbedding G id) (U : Set Plane)
    (hout : ∀ x y, G.Adj x y → Disjoint (segment ℝ x y) U)
    (hin : ∀ i, openSegmentTrace (a i) (b i) ⊆ U)
    (hdisj : ∀ i j, i ≠ j → Disjoint (segment ℝ (a i) (b i)) (segment ℝ (a j) (b j)))
    (hend : ∀ i x y, G.Adj x y →
      (a i ∈ segment ℝ x y → a i=x ∨ a i=y) ∧
      (b i ∈ segment ℝ x y → b i=x ∨ b i=y)) :
    StraightEdgeEmbedding (segmentAugmentedGraph G a b hne) id := by
  refine ⟨Function.injective_id,?_⟩
  intro x y z w hxy hzw r hrx hrz
  rcases hxy with hxy | ⟨i,hi⟩ <;> rcases hzw with hzw | ⟨j,hj⟩
  · exact hemb.2 x y z w hxy hzw r hrx hrz
  · have hchord : r ∈ segment ℝ (a j) (b j) := by
      rcases hj with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
      · exact hrz
      · simpa only [id_eq,segment_symm] using hrz
    obtain ⟨hold,hnew⟩ := exterior_segment_chord_meeting G U (a j) (b j) x y r hxy hout
      (hin j) (hend j x y hxy).1 (hend j x y hxy).2 hrx hchord
    have hrzw : r=z ∨ r=w := by
      rcases hj with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
      · exact hnew
      · exact hnew.symm
    exact Or.inr (Or.inr (common_endpoint_alternatives x y z w r hold hrzw))
  · have hchord : r ∈ segment ℝ (a i) (b i) := by
      rcases hi with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
      · exact hrx
      · simpa only [id_eq,segment_symm] using hrx
    obtain ⟨hold,hnew⟩ := exterior_segment_chord_meeting G U (a i) (b i) z w r hzw hout
      (hin i) (hend i z w hzw).1 (hend i z w hzw).2 hrz hchord
    have hrxy : r=x ∨ r=y := by
      rcases hi with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
      · exact hnew
      · exact hnew.symm
    exact Or.inr (Or.inr (common_endpoint_alternatives x y z w r hrxy hold))
  · by_cases hij : i=j
    · subst j
      rcases hi with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> rcases hj with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
      · exact Or.inl ⟨rfl,rfl⟩
      · exact Or.inr (Or.inl ⟨rfl,rfl⟩)
      · exact Or.inr (Or.inl ⟨rfl,rfl⟩)
      · exact Or.inl ⟨rfl,rfl⟩
    · apply False.elim
      apply Set.disjoint_left.mp (hdisj i j hij)
      · rcases hi with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
        · exact hrx
        · simpa only [id_eq,segment_symm] using hrx
      · rcases hj with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
        · exact hrz
        · simpa only [id_eq,segment_symm] using hrz

end Zarankiewicz

end

end OAI
