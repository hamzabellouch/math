import OAI.Geometry.TranslativeCovering.LensQuantitative

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal

universe u_1

namespace BlockTerminal
open Finset
variable {I : Type u_1} [Fintype I] [DecidableEq I]

lemma merge_exists (P : Finpartition (univ : Finset I))
    (H : Finset (Finset I)) (hH : H ⊆ P.parts) (hH2 : 2 ≤ H.card) :
    ∃ Q : Finpartition (univ : Finset I),
      Q.parts = insert (H.biUnion id) (P.parts \ H) ∧ Q.parts.card < P.parts.card := by
  classical
  let W := H.biUnion id
  have hHne : H.Nonempty := card_pos.mp (by omega)
  have hW : W.Nonempty := by
    obtain ⟨A, hAH⟩ := hHne
    obtain ⟨i, hi⟩ := P.nonempty_of_mem_parts (hH hAH)
    exact ⟨i, mem_biUnion.mpr ⟨A, hAH, hi⟩⟩
  have hcover (i : I) : ∃! A, A ∈ insert W (P.parts \ H) ∧ i ∈ A := by
    obtain ⟨A, hA, hiA⟩ := P.exists_mem (mem_univ i)
    by_cases hAH : A ∈ H
    · refine ⟨W, ⟨mem_insert_self _ _, mem_biUnion.mpr ⟨A, hAH, hiA⟩⟩, ?_⟩
      rintro B ⟨hB, hiB⟩
      rcases mem_insert.mp hB with rfl | hB
      · rfl
      · have hBA := P.eq_of_mem_parts (mem_sdiff.mp hB).1 hA hiB hiA
        exact False.elim ((mem_sdiff.mp hB).2 (hBA ▸ hAH))
    · refine ⟨A, ⟨mem_insert_of_mem (mem_sdiff.mpr ⟨hA,hAH⟩), hiA⟩, ?_⟩
      rintro B ⟨hB, hiB⟩
      rcases mem_insert.mp hB with hBW | hB
      · rw [hBW] at hiB
        obtain ⟨C, hCH, hiC⟩ := mem_biUnion.mp hiB
        have hCA := P.eq_of_mem_parts (hH hCH) hA hiC hiA
        exact False.elim (hAH (hCA ▸ hCH))
      · exact P.eq_of_mem_parts (mem_sdiff.mp hB).1 hA hiB hiA
  let Q := Finpartition.ofExistsUnique (insert W (P.parts \ H))
    (fun _ _ => subset_univ _) (fun i _ => hcover i) (by
      simp only [Finset.mem_insert, Finset.mem_sdiff, not_or]
      exact ⟨fun he => hW.ne_empty he.symm, fun h => P.empty_notMem_parts h.1⟩)
  refine ⟨Q, rfl, ?_⟩
  change (insert W (P.parts \ H)).card < P.parts.card
  have hcard := card_sdiff_add_card_eq_card hH
  have hins := card_insert_le W (P.parts \ H)
  omega

lemma exists_terminal (Good : Finset I → Prop) (hsingle : ∀ i, Good {i}) :
    ∃ P : Finpartition (univ : Finset I),
      (∀ S ∈ P.parts, Good S) ∧
      ∀ H ⊆ P.parts, 2 ≤ H.card → ¬Good (H.biUnion id) := by
  classical
  have hex : ∃ k : ℕ, ∃ P : Finpartition (univ : Finset I),
      (∀ S ∈ P.parts, Good S) ∧ P.parts.card = k := by
    refine ⟨(⊥ : Finpartition (univ : Finset I)).parts.card, ⊥, ?_, rfl⟩
    intro S hS
    rw [Finpartition.parts_bot] at hS
    obtain ⟨i, _, hi⟩ := mem_map.mp hS
    simpa only [Function.Embedding.coeFn_mk, ← hi] using hsingle i
  obtain ⟨P, hP, hc⟩ := Nat.find_spec hex
  refine ⟨P, hP, ?_⟩
  intro H hH hH2 hg
  obtain ⟨Q, hQ, hlt⟩ := merge_exists P H hH hH2
  have hQgood : ∀ S ∈ Q.parts, Good S := by
    intro S hS
    rw [hQ] at hS
    rcases mem_insert.mp hS with rfl | hS
    · exact hg
    · exact hP S (mem_sdiff.mp hS).1
  have hmin := Nat.find_min' hex ⟨Q, hQgood, rfl⟩
  omega

end BlockTerminal

end OAI
