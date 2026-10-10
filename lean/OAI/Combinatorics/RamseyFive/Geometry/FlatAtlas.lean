import Mathlib

namespace OAI

namespace SharpRamseyFive.FlatAtlas

section
open Module
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Finite K]

omit [FiniteDimensional K V] [Finite K] in
lemma exists_rank_submodule (r : ℕ) (hr : r ≤ finrank K V) :
    ∃ A : Submodule K V, finrank K A = r := by
  obtain ⟨s, hcard, hs⟩ := exists_finset_linearIndependent_of_le_finrank (R := K) (M := V) hr
  refine ⟨Submodule.span K (s : Set V), ?_⟩
  rw [finrank_span_finset_eq_card (show LinearIndepOn K id (s : Set V) from hs)]
  exact hcard

lemma exists_atlas (r : ℕ) (hr : r ≤ finrank K V) :
    ∃ (m : ℕ) (_ : 0 < m) (P : Fin m → Submodule K V),
      (∀ i, finrank K (P i) = r) ∧
      ∀ A : Submodule K V, finrank K A = r → ∃ i, P i = A := by
  classical
  let : Finite V := Module.finite_of_finite K
  let T := {A : Submodule K V // finrank K A = r}
  let : Fintype T := Fintype.ofFinite T
  obtain ⟨A,hA⟩ := exists_rank_submodule (K := K) (V := V) r hr
  let : Nonempty T := ⟨⟨A,hA⟩⟩
  let e := (Fintype.equivFin T).symm
  refine ⟨Fintype.card T, Fintype.card_pos, fun i => (e i).val, ?_, ?_⟩
  · intro i
    exact (e i).property
  · intro B hB
    refine ⟨e.symm ⟨B,hB⟩, ?_⟩
    simp
end

open Module
open scoped Classical
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

lemma exists_spanning_code (A : Submodule K V) (n : ℕ) (hn : finrank K V≤n) :
    ∃f : Fin n→V,Submodule.span K (Set.range f)=A := by
  obtain ⟨f,hf,hs,-⟩ := Submodule.exists_fun_fin_finrank_span_eq K (A : Set V)
  have hs' : Submodule.span K (Set.range f)=A := hs.trans (Submodule.span_eq _)
  have hr : finrank K (Submodule.span K (A : Set V))≤n := (Submodule.finrank_le _).trans hn
  let g : Fin n→V := fun i=>if hi : i.val<finrank K (Submodule.span K (A : Set V)) then f ⟨i.val,hi⟩ else 0
  refine ⟨g,le_antisymm (Submodule.span_le.mpr ?_) ?_⟩
  · rintro v ⟨i,rfl⟩
    dsimp only [g]
    split_ifs with hi
    · exact hf _
    · exact A.zero_mem
  · apply hs'.symm.le.trans
    apply Submodule.span_mono
    rintro v ⟨i,rfl⟩
    refine ⟨i.castLE hr,?_⟩
    simp only [g,Fin.val_castLE,dite_eq_left i.prop]

noncomputable def flatCode (n : ℕ) (hn : finrank K V≤n) (A : Submodule K V) : Fin n→V :=
  (exists_spanning_code A n hn).choose

lemma decode_flatCode (n : ℕ) (hn : finrank K V≤n) (A : Submodule K V) :
    Submodule.span K (Set.range (flatCode n hn A))=A :=
  (exists_spanning_code A n hn).choose_spec

lemma flatCode_injective (n : ℕ) (hn : finrank K V≤n) : Function.Injective (flatCode n hn (K:=K) (V:=V)) := by
  intro A B hab
  rw [←decode_flatCode n hn A,←decode_flatCode n hn B,hab]

theorem card_submodules_le [Finite K] (n : ℕ) (hn : finrank K V≤n) :
    Nat.card (Submodule K V)≤(Nat.card V)^n := by
  let : Finite V := Module.finite_of_finite K
  have hh := Nat.card_le_card_of_injective (flatCode n hn (K:=K) (V:=V)) (flatCode_injective n hn)
  simpa only [Nat.card_fun,Nat.card_fin] using hh

end SharpRamseyFive.FlatAtlas

end OAI
