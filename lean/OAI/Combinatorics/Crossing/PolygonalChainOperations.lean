import OAI.Combinatorics.Crossing.PolygonalChainExistence
import OAI.Combinatorics.Crossing.PolygonComposition

namespace OAI

noncomputable section
namespace Zarankiewicz.PolygonalChain
variable {O : Set Plane} {a b c : Plane}

theorem vertex_mem (P : PolygonalChain O a b) (i : ℕ) (hi : i ≤ P.pieces) : P.vertices i ∈ O := by
  by_cases h0 : i=0
  · subst i
    rw [P.first]
    exact P.start_mem
  · have hp : 0 < i := by omega
    have hh := P.inside (i-1) (by omega) (right_mem_segment ℝ (P.vertices (i-1)) (P.vertices (i-1+1)))
    simpa [Nat.sub_add_cancel (show 1 ≤ i by omega)] using hh

def single (O : Set Plane) (a b : Plane) (ha : a ∈ O) (h : segment ℝ a b ⊆ O) : PolygonalChain O a b where
  pieces := 1
  vertices := fun i => if i=0 then a else b
  first := by simp
  last := by simp
  start_mem := ha
  inside := by
    intro i hi
    have he : i = 0 := by omega
    subst i
    simpa using h

def take (P : PolygonalChain O a b) (k : ℕ) (hk : k ≤ P.pieces) : PolygonalChain O a (P.vertices k) where
  pieces := k
  vertices := P.vertices
  first := P.first
  last := rfl
  start_mem := P.start_mem
  inside := fun i hi => P.inside i (by omega)

def drop (P : PolygonalChain O a b) (k : ℕ) (hk : k ≤ P.pieces) : PolygonalChain O (P.vertices k) b where
  pieces := P.pieces-k
  vertices := fun i => P.vertices (k+i)
  first := by simp
  last := by simpa [Nat.add_sub_of_le hk] using P.last
  start_mem := P.vertex_mem k hk
  inside := by
    intro i hi
    simpa [Nat.add_assoc] using P.inside (k+i) (by omega)

def join (P : PolygonalChain O a b) (Q : PolygonalChain O b c) : PolygonalChain O a c where
  pieces := P.pieces+Q.pieces
  vertices := joinedSequence P.vertices Q.vertices P.pieces
  first := (joinedSequence_left _ _ _ (P.last.trans Q.first.symm) 0 (Nat.zero_le _)).trans P.first
  last := (joinedSequence_right _ _ P.pieces Q.pieces).trans Q.last
  start_mem := P.start_mem
  inside := by
    intro i hi
    have hglue : P.vertices P.pieces=Q.vertices 0 := P.last.trans Q.first.symm
    by_cases hin : i < P.pieces
    · rw [joinedSequence_left _ _ _ hglue i (by omega),joinedSequence_left _ _ _ hglue (i+1) (by omega)]
      exact P.inside i hin
    · have hbase : i=P.pieces+(i-P.pieces) := by omega
      have hnext : i+1=P.pieces+((i-P.pieces)+1) := by omega
      have h₀ : joinedSequence P.vertices Q.vertices P.pieces i = Q.vertices (i-P.pieces) := by
        conv_lhs => rw [hbase]
        exact joinedSequence_right _ _ _ _
      have h₁ : joinedSequence P.vertices Q.vertices P.pieces (i+1) = Q.vertices ((i-P.pieces)+1) := by
        rw [hnext, joinedSequence_right]
      rw [h₀,h₁]
      exact Q.inside (i-P.pieces) (by omega)

@[simp] theorem pieces_single (ha : a ∈ O) (h : segment ℝ a b ⊆ O) : (single O a b ha h).pieces=1 := rfl
@[simp] theorem pieces_take (P : PolygonalChain O a b) (k : ℕ) (hk : k ≤ P.pieces) : (P.take k hk).pieces=k := rfl
@[simp] theorem pieces_drop (P : PolygonalChain O a b) (k : ℕ) (hk : k ≤ P.pieces) : (P.drop k hk).pieces=P.pieces-k := rfl
@[simp] theorem pieces_join (P : PolygonalChain O a b) (Q : PolygonalChain O b c) : (P.join Q).pieces=P.pieces+Q.pieces := rfl

end Zarankiewicz.PolygonalChain

end

end OAI
