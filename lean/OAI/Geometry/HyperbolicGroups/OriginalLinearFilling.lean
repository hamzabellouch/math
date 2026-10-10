import Mathlib
import OAI.Geometry.HyperbolicGroups.RelativeGlobalStep
import OAI.Geometry.HyperbolicGroups.RelativeSmallPartition

namespace OAI

noncomputable section

namespace HyperbolicObstruction.ConeSkeleton
open IncidenceTemplate CoreGeometry LetterPresentation PictureSwitch WordPictures
open Occurrences.Shape
attribute [local instance] Classical.propDecidable

/-- Deterministic linear filling theorem, with a uniform cutoff for
all random tables and all original-letter null words, including the empty word. -/
theorem original_letter_linear_filling {α β δ : ℝ}
    (ha : 0 < α) (hb : 7*α < β) (hd : 0 < δ) :
    ∃ M : ℕ, 0 < M ∧ ∀ (n : ℕ)
      (w : TableModel.Entry (A := Alphabet n) rowSupport → Bool)
      (d : (Fin 6 → Alphabet n) → Bool),
      Occurrences.GoodUpTo M α β δ (Sum.elim w d) →
      ∀ (ell : ℕ) (word : Fin ell → Alphabet n),
      PresentedGroup.mk (Relator n w d) (FreeGroup.mk (List.ofFn word)) = 1 →
      ∃ a, Homotopy (SimpleWordRelator n w d) (List.ofFn word) [] a ∧
        defectConstant α β δ * a ≤ 60 * (ell : ℝ) := by
  have hk := defectConstant_pos ha hb hd
  obtain ⟨K,hK,hpart⟩ := RelDisk.uniform_small_interior_partition
    (defectConstant α β δ / 4) (div_pos hk (by norm_num))
  refine ⟨8*K,Nat.mul_pos (by decide) hK,?_⟩
  intro n w d hgood ell word hnull
  rcases Nat.eq_zero_or_pos ell with he | hell
  · subst ell
    refine ⟨0,?_,by simp⟩
    simpa only [List.ofFn_zero] using (WordPictures.Homotopy.refl (R := SimpleWordRelator n w d) [])
  let c : Top n w → MacroGraph.graph.Dart → ℤ := fun _ _ => 0
  have hc : ∀ a e, c a e.symm = -c a e := by intros; simp [c]
  let f : FrozenCell n w d → ℤ := fun _ => 0
  obtain ⟨P,xs,hm,hs,hbig,hred,hrad,hboundary,hword,htag,_hor⟩ :=
    null_letter_word_normal_picture n w d ell word hell c hc f hnull
  obtain ⟨I,inst,part,hsize,hcut⟩ := hpart n w d ell hell word c hc f P hs hbig hm
  let := inst
  have hM (i : I) : 8 * Fintype.card
      {F : RelDisk.InteriorFace n w d ell hell word c hc f P // part F.val = i} ≤ 8*K :=
    Nat.mul_le_mul_left 8 (hsize i)
  have hface := RelDisk.partition_face_bound n w d ell hell word c hc f P xs hword htag
    part ha.le hgood hs hm hred hrad hbig hM
  obtain ⟨a,hfill,ha'⟩ := RelDisk.partition_filling_bound n w d ell hell word c hc f P
    xs hboundary hword htag part ha.le hk.le hgood hs hm hred hrad hbig hM
  refine ⟨a,hfill,?_⟩
  nlinarith

/-- The same theorem in list-word form, with an explicit positive
linear constant depending only on the fixed parameters. -/
theorem original_letter_linear_filling_list {α β δ : ℝ}
    (ha : 0 < α) (hb : 7*α < β) (hd : 0 < δ) :
    ∃ (M : ℕ) (C : ℝ), 0 < M ∧ 0 < C ∧ ∀ (n : ℕ)
      (w : TableModel.Entry (A := Alphabet n) rowSupport → Bool)
      (d : (Fin 6 → Alphabet n) → Bool),
      Occurrences.GoodUpTo M α β δ (Sum.elim w d) →
      ∀ word : List (Alphabet n),
      PresentedGroup.mk (Relator n w d) (FreeGroup.mk word) = 1 →
      ∃ a, Homotopy (SimpleWordRelator n w d) word [] a ∧ (a : ℝ) ≤ C * word.length := by
  obtain ⟨M,hM,hh⟩ := original_letter_linear_filling ha hb hd
  have hk := defectConstant_pos ha hb hd
  refine ⟨M,60 / defectConstant α β δ,hM,div_pos (by norm_num) hk,?_⟩
  intro n w d hgood word hnull
  have he : List.ofFn word.get = word := List.ofFn_get word
  obtain ⟨a,hfill,ha'⟩ := hh n w d hgood word.length word.get (by rwa [he])
  refine ⟨a,he ▸ hfill,?_⟩
  calc
    (a : ℝ) ≤ (60 * word.length) / defectConstant α β δ :=
      (le_div_iff₀ hk).mpr (by nlinarith)
    _ = _ := by ring

end HyperbolicObstruction.ConeSkeleton
end

end OAI
