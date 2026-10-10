import Mathlib

namespace OAI

noncomputable section

section

noncomputable section

open Set

namespace Kadison.CompactInvariant

variable {G E : Type*} [Monoid G] [TopologicalSpace E] [T2Space E] [MulAction G E]

def Invariant (S : Set E) : Prop := ∀ g : G,∀ x∈S,g • x∈S

omit [TopologicalSpace E] [T2Space E] in
lemma invariant_sInter {F : Set (Set E)} (hF : ∀ S∈F,Invariant (G:=G) S) :
    Invariant (G:=G) (⋂₀ F) := by
  intro g x hx
  exact fun S hS => hF S hS g x (hx S hS)

theorem exists_minimal {C : Set E} (hC : IsCompact C) (hne : C.Nonempty)
    (hinv : Invariant (G:=G) C) (P : Set E → Prop) (hP : P C)
    (hPi : ∀ F : Set (Set E),F.Nonempty → (∀ S∈F,P S) → P (⋂₀ F)) :
    ∃ K : Set E,Minimal (fun S => S⊆C ∧ S.Nonempty ∧ IsClosed S ∧
      Invariant (G:=G) S ∧ P S) K := by
  apply zorn_superset
  intro F hFC hF
  obtain rfl | hFn := F.eq_empty_or_nonempty
  · exact ⟨C,⟨subset_rfl,hne,hC.isClosed,hinv,hP⟩,by simp⟩
  have hsub : ⋂₀ F⊆C := by
    obtain ⟨S,hS⟩ := hFn
    exact (sInter_subset_of_mem hS).trans (hFC hS).1
  have hneI : (⋂₀ F).Nonempty := by
    have : Nonempty F := hFn.to_subtype
    rw [sInter_eq_iInter]
    apply IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed
    · intro S T
      obtain hST | hTS := hF.total S.property T.property
      · exact ⟨S,subset_rfl,hST⟩
      · exact ⟨T,hTS,subset_rfl⟩
    · exact fun S => (hFC S.property).2.1
    · exact fun S => hC.of_isClosed_subset (hFC S.property).2.2.1 (hFC S.property).1
    · exact fun S => (hFC S.property).2.2.1
  refine ⟨⋂₀ F,⟨hsub,hneI,isClosed_sInter (fun S hS => (hFC hS).2.2.1),
    invariant_sInter (fun S hS => (hFC hS).2.2.2.1),hPi F hFn (fun S hS => (hFC hS).2.2.2.2)⟩,?_⟩
  exact fun S hS => sInter_subset_of_mem hS

lemma exists_minimal_compact {C : Set E} (hC : IsCompact C) (hne : C.Nonempty)
    (hinv : Invariant (G:=G) C) :
    ∃ K : Set E,Minimal (fun S => S⊆C ∧ S.Nonempty ∧ IsClosed S ∧
      Invariant (G:=G) S) K := by
  obtain ⟨K,hK⟩ := exists_minimal hC hne hinv (fun _ => True) trivial (by simp)
  refine ⟨K,⟨⟨hK.prop.1,hK.prop.2.1,hK.prop.2.2.1,hK.prop.2.2.2.1⟩,?_⟩⟩
  intro S hS hSK
  exact hK.le_of_le ⟨hS.1,hS.2.1,hS.2.2.1,hS.2.2.2,trivial⟩ hSK

variable [AddCommGroup E] [Module ℝ E]

lemma exists_minimal_convex {C : Set E} (hC : IsCompact C) (hne : C.Nonempty)
    (hinv : Invariant (G:=G) C) (hconv : Convex ℝ C) :
    ∃ K : Set E,Minimal (fun S => S⊆C ∧ S.Nonempty ∧ IsClosed S ∧
      Invariant (G:=G) S ∧ Convex ℝ S) K :=
  exists_minimal hC hne hinv (Convex ℝ) hconv (fun _ _ h => convex_sInter h)

end Kadison.CompactInvariant

end

end
end

end OAI
