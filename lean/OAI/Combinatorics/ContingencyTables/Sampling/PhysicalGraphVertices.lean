import OAI.Combinatorics.ContingencyTables.Transport.ContextGraphMembership

namespace OAI

/-! # Finite physical vertices containing every contextual transport leaf -/

namespace ContingencyTables.SmallGraphProfiles

open scoped BigOperators Classical
open SmallContextCoordinates SmallContextEnumeration SmallContextFibres
open PhysicalCompletionFibres LargePairEnumeration BalancedFamily BalancedBox
open IntegerWeightedTransport FirstPaperProfiles ExcessContextProfiles

universe u

variable {I J : Type u} [Fintype I] [Fintype J] [LinearOrder I] [LinearOrder J]

noncomputable instance profilesFintype (small : I → J → Bool) (B : I → J → ℕ) :
    Fintype (Profiles small B) := by unfold Profiles; infer_instance

noncomputable def vertices (small : I → J → Bool) (B : I → J → ℕ) : Finset (SmallProfile small) :=
  Finset.univ.image (fun z : Profiles small B => naturalProfile z.val)

lemma mem_vertices_iff (small : I → J → Bool) (B : I → J → ℕ) (z : SmallProfile small) :
    z ∈ vertices small B ↔ (∀ a, z a ≤ B a.1.val.1 a.1.val.2) ∧ Pattern small B z := by
  constructor
  · intro hz
    obtain ⟨p,_,rfl⟩ := Finset.mem_image.mp hz
    exact ⟨naturalProfile_bounded p.val,p.property⟩
  · rintro ⟨hb,hp⟩
    let p : BoundedProfile small B := fun a => ⟨z a,Nat.lt_succ_of_le (hb a)⟩
    let q : Profiles small B := ⟨p,hp⟩
    exact Finset.mem_image.mpr ⟨q,Finset.mem_univ _,rfl⟩

/-- Every vertex used by the common conditional energy is an actual
bounded allowed small-graph profile after the physical coordinate map. -/
theorem context_vertex_mem (small : I → J → Bool) (B : I → J → ℕ)
    (s : I×J) (hs : small s.1 s.2=true) (σ : I×J → ℕ) (U : ℕ)
    (hU : 1 ≤ U) (hB : ∀ i j, small i j=true → B i j=U)
    (hσ : ∀ a : Earlier small s, σ a.val.val ≤ U) {n : ℕ} (e : Fin n ≃ Later small s)
    (x : Coordinates Bool (widths (fun _ : Fin n => U)) → ℕ)
    (hx : x ∈ contextVertices U n)
    (hbox : InBox (bounds (fun _ : Bool => U) (widths (fun _ : Fin n => U))) x) :
    assemble small s hs σ U e x ∈ vertices small B := by
  obtain ⟨l,_,hx⟩ := Finset.mem_biUnion.mp hx
  apply (mem_vertices_iff small B _).mpr
  refine ⟨?_,leaf_pattern small B s hs σ U l.val hU (Nat.le_of_lt_succ l.isLt) hB hσ e x hx hbox⟩
  intro a
  rw [hB _ _ a.1.property]
  exact assemble_bounded small s hs σ U hσ e x hbox a

end ContingencyTables.SmallGraphProfiles

end OAI
