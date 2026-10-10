import OAI.Combinatorics.Ramsey.CycleClique.Construction.InteriorSystemSelection
import OAI.Combinatorics.Ramsey.CycleClique.Construction.RawOrientations

namespace OAI

/-! Each selected internal vertex is a representative in one orientation;
vertices in different components may be oriented independently. -/

namespace CycleClique.Construction
open scoped Classical

variable {V : Type*} {G : SimpleGraph V} {Q : Finset V}

namespace SystemAssignedAmounts

theorem profile_of_mem {C : List (List V)} {w : List ℕ}
    (h : SystemAssignedAmounts Q C w) {l : List V} (hl : l ∈ C) :
    ∃ a, AssignedAmounts Q l a ∧ ∀ x ∈ a, x ∈ w := by
  induction h with
  | nil => simp at hl
  | @cons l' C a w ha hw ih =>
    rcases List.mem_cons.mp hl with rfl | hl
    · exact ⟨a, ha, fun x hx => List.mem_append_left _ hx⟩
    · obtain ⟨a', ha', hsub⟩ := ih hl
      exact ⟨a', ha', fun x hx => List.mem_append_right _ (hsub x hx)⟩

end SystemAssignedAmounts

theorem selectedChain_orientation {l : List V} {w : List ℕ}
    (h : AssignedAmounts Q l w) (hmin : ∀ a ∈ w, 2 ≤ a) {x : V}
    (hx : x ∈ selectedChain Q l) :
    ∃ b : Bool, x ∈ chainRepresentatives Q (RawPathSystem.orientedChain (fun _ => b) l) := by
  by_cases hl : l.length = 4
  · obtain ⟨q, u, v, r, rfl, hq, hr, hu, hv⟩ :=
      h.amount_two_shape (amount_profile_eq_two_of_length_four h hl hmin)
    have hx' : x = u ∨ x = v := by simpa [selectedChain] using hx
    rcases hx' with rfl | rfl
    · exact ⟨false, by simp [RawPathSystem.orientedChain, chainRepresentatives,
        representativesFrom, hq, hu, hv]⟩
    · exact ⟨true, by simp [RawPathSystem.orientedChain, chainRepresentatives,
        representativesFrom, hr, hu, hv]⟩
  · refine ⟨false, ?_⟩
    have hh : x ∈ interiorRepresentatives Q l := by simpa [selectedChain, hl] using hx
    exact List.mem_of_mem_tail hh

namespace RawPathSystem

theorem representative_of_oriented_chain (S : RawPathSystem G Q) (p : List V → Bool)
    {l : List V} (hl : l ∈ S.chains) {x : V}
    (hx : x ∈ chainRepresentatives Q (orientedChain p l)) :
    x ∈ (S.orientChains p).representatives := by
  apply List.mem_flatten.mpr
  refine ⟨chainRepresentatives Q (orientedChain p l), ?_, hx⟩
  apply List.mem_map.mpr
  refine ⟨orientedChain p l, ?_, rfl⟩
  exact List.mem_map.mpr ⟨l, hl, rfl⟩

theorem joint_orientation (S : RawPathSystem G Q) {l m : List V}
    (hl : l ∈ S.chains) (hm : m ∈ S.chains) (hne : l ≠ m)
    {x y : V} (bx by_ : Bool)
    (hx : x ∈ chainRepresentatives Q (orientedChain (fun _ => bx) l))
    (hy : y ∈ chainRepresentatives Q (orientedChain (fun _ => by_) m)) :
    ∃ p : List V → Bool, x ∈ (S.orientChains p).representatives ∧
      y ∈ (S.orientChains p).representatives := by
  classical
  let p := fun z : List V => if z = l then bx else if z = m then by_ else false
  have hpl : p l = bx := by simp [p]
  have hpm : p m = by_ := by simp [p, hne.symm]
  refine ⟨p, S.representative_of_oriented_chain p hl ?_,
    S.representative_of_oriented_chain p hm ?_⟩
  · simpa only [orientedChain, hpl] using hx
  · simpa only [orientedChain, hpm] using hy

end RawPathSystem

end CycleClique.Construction

end OAI
