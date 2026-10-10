import OAI.NumberTheory.Ostmann.Characters.CharacterTargetCellData
import OAI.NumberTheory.Ostmann.Tree.CellGroupPigeonhole

namespace OAI

/-! # Fixing the actual target shells and their ordered cell lists -/
namespace Ostmann
open scoped Classical BigOperators

noncomputable def CharacterTargetWord.code {P : Finset ℕ} {F : ℕ → ℂ}
    {c δ U : ℝ} {k : ℕ} {T : ℝ} (w : CharacterTargetWord P F c δ U k T) : List ℕ :=
  w.shell :: w.indices

theorem CharacterTargetWord.index_le {P : Finset ℕ} {F : ℕ → ℂ}
    {c δ U : ℝ} {k : ℕ} {T : ℝ} (w : CharacterTargetWord P F c δ U k T)
    (hc : 0 < c) (hδ : 0 < δ) (B : ℕ) (hP : ∀ p ∈ P, primeLogIndex p ≤ B)
    (h : ℕ) (hh : h ∈ w.indices) : h ≤ B := by
  have hm : 0 < ∑ p ∈ w.cell h, (p : ℝ)⁻¹ :=
    (by positivity : 0 < δ * c / (32 * Real.exp (U + w.shell))).trans_le (w.cell_mass h hh)
  have hs : (w.cell h).Nonempty := by
    by_contra hn
    have he := Finset.not_nonempty_iff_eq_empty.mp hn
    simp only [he, Finset.sum_empty, lt_self_iff_false] at hm
  obtain ⟨p, hp⟩ := hs
  have hi := (Finset.mem_filter.mp hp).2
  simpa only [hi] using hP p (w.cell_subset h hp)

theorem CharacterTargetWord.cell_eq_of_code {P : Finset ℕ} {F G : ℕ → ℂ}
    {c δ U : ℝ} {k : ℕ} {T S : ℝ}
    (w : CharacterTargetWord P F c δ U k T) (v : CharacterTargetWord P G c δ U k S)
    (hcode : w.code = v.code) (h : ℕ) : w.cell h = v.cell h := by
  have he : w.shell = v.shell := (List.cons.inj hcode).1
  simp only [CharacterTargetWord.cell, he]

noncomputable def characterTargetCodeGroups {P : Finset ℕ} {F : ℕ → ℂ}
    {c δ U : ℝ} {k : ℕ} {T : Option (Fin k) → ℝ}
    (w : ∀ j, CharacterTargetWord P F c δ U k (T j)) : List (List ℕ) :=
  List.ofFn (fun i : Fin (k + 1) => (w (finSuccEquiv k i)).code)

theorem characterTargetCodeGroups_length {P : Finset ℕ} {F : ℕ → ℂ}
    {c δ U : ℝ} {k : ℕ} {T : Option (Fin k) → ℝ}
    (w : ∀ j, CharacterTargetWord P F c δ U k (T j)) :
    (characterTargetCodeGroups w).length = k + 1 := by
  simp [characterTargetCodeGroups]

theorem characterTargetCodeGroups_size {P : Finset ℕ} {F : ℕ → ℂ}
    {c δ U : ℝ} {k : ℕ} {T : Option (Fin k) → ℝ}
    (w : ∀ j, CharacterTargetWord P F c δ U k (T j)) :
    ((characterTargetCodeGroups w).map List.length).sum =
      (∑ j : Option (Fin k), (w j).indices.length) + (k + 1) := by
  simp only [characterTargetCodeGroups, List.map_ofFn, List.sum_ofFn,
    CharacterTargetWord.code, Function.comp_def, List.length_cons]
  rw [Finset.sum_add_distrib]
  have he := Equiv.sum_comp (finSuccEquiv k) (fun j => (w j).indices.length)
  simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one] using
    congrArg (fun n : ℕ => n + (k + 1)) he

theorem characterTargetCodeGroups_data {P : Finset ℕ} {F G : ℕ → ℂ}
    {c δ U : ℝ} {k : ℕ} {T S : Option (Fin k) → ℝ}
    (w : ∀ j, CharacterTargetWord P F c δ U k (T j))
    (v : ∀ j, CharacterTargetWord P G c δ U k (S j))
    (he : characterTargetCodeGroups w = characterTargetCodeGroups v) :
    ∀ j, (w j).shell = (v j).shell ∧ (w j).indices = (v j).indices := by
  change List.ofFn (fun i : Fin (k + 1) => (w (finSuccEquiv k i)).code) =
    List.ofFn (fun i : Fin (k + 1) => (v (finSuccEquiv k i)).code) at he
  have he' := List.ofFn_injective he
  intro j
  have hc := congrFun he' ((finSuccEquiv k).symm j)
  have hj := (finSuccEquiv k).apply_symm_apply j
  rw [hj] at hc
  exact List.cons.inj hc

theorem characterTargetCodeGroups_cells {P : Finset ℕ} {F G : ℕ → ℂ}
    {c δ U : ℝ} {k : ℕ} {T S : Option (Fin k) → ℝ}
    (w : ∀ j, CharacterTargetWord P F c δ U k (T j))
    (v : ∀ j, CharacterTargetWord P G c δ U k (S j))
    (he : characterTargetCodeGroups w = characterTargetCodeGroups v) :
    ∀ j h, (w j).cell h = (v j).cell h := by
  intro j h
  have hs := (characterTargetCodeGroups_data w v he j).1
  simp only [CharacterTargetWord.cell, hs]

/-- Shell identifiers are part of the code, so fixing it fixes the actual
prime sets even when targets and Fourier tests vary with the endpoint. -/
theorem common_character_target_cells (E : Finset ℕ) (hE : E.Nonempty)
    (P : Finset ℕ) (F : ℕ → ℕ → ℂ) (c δ U : ℝ) (k N B : ℕ)
    (T : ℕ → Option (Fin k) → ℝ)
    (w : ∀ a j, CharacterTargetWord P (F a) c δ U k (T a j))
    (hc : 0 < c) (hδ : 0 < δ) (hk : 5 * k ≤ B)
    (hP : ∀ p ∈ P, primeLogIndex p ≤ B)
    (hN : ∀ a ∈ E, (∑ j : Option (Fin k), (w a j).indices.length) ≤ N) :
    ∃ S : Finset ℕ, S ⊆ E ∧ S.Nonempty ∧
      E.card ≤ ((N + (k + 1) + (k + 1) + 1) *
        (max (N + (k + 1)) B + 1) ^ (N + (k + 1) + (k + 1))) * S.card ∧
      ∀ a ∈ S, ∀ b ∈ S, ∀ j,
        (w a j).indices = (w b j).indices ∧ ∀ h, (w a j).cell h = (w b j).cell h := by
  obtain ⟨v, S, hSE, hS, hcard, hsame⟩ := common_cell_groups E hE (k + 1) (N + (k + 1)) B
    (fun a => characterTargetCodeGroups (w a))
    (fun a _ => characterTargetCodeGroups_length (w a))
    (fun a ha => by rw [characterTargetCodeGroups_size]; exact Nat.add_le_add_right (hN a ha) _)
    (by
      intro a _ l hl h hh
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hl
      rcases List.mem_cons.mp hh with hs | hi
      · subst h
        exact (w a _).shell_le.trans hk
      · exact (w a _).index_le hc hδ B hP h hi)
  refine ⟨S, hSE, hS, hcard, ?_⟩
  intro a ha b hb j
  have he := (hsame a ha).trans (hsame b hb).symm
  exact ⟨(characterTargetCodeGroups_data (w a) (w b) he j).2,
    characterTargetCodeGroups_cells (w a) (w b) he j⟩

end Ostmann

end OAI
