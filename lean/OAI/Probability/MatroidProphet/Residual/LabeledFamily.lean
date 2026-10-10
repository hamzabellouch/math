import OAI.Probability.MatroidProphet.Residual.Witnesses

namespace OAI

namespace MatroidProphet
open Set Finset Pivots
variable {α : Type*} [Fintype α] [LinearOrder α]

noncomputable def groupLabel (U : Finset α) (i : Fin U.card) : α := (U.equivFin.symm i).val

lemma groupLabel_mem
    {α : Type u_1} [Fintype α] [LinearOrder α] (U : Finset α) (i : Fin U.card) :
    groupLabel U i ∈ U :=
  (U.equivFin.symm i).property

lemma exists_groupLabel
    {α : Type u_1} [Fintype α] [LinearOrder α] (U : Finset α) {e : α} (he : e ∈ U) :
    ∃ i, groupLabel U i = e := by
  refine ⟨U.equivFin ⟨e, he⟩, ?_⟩
  simp [groupLabel]

noncomputable def labeledResidualFamily (M : Matroid α) (U : Finset α) (κ : ℕ)
    (F : ℤ → Set α) (a : ℤ) (ε : Fin 2) (K : ParityWindow a ε → Set α) : Finset (Finset α) :=
  (integerResidualFamily M U (U.card / κ) F a ε K (groupLabel U)).image
    (fun R => R.image (groupLabel U))

lemma labeledResidualFamily_subsets (M : Matroid α) (U : Finset α) (κ : ℕ)
    (F : ℤ → Set α) (a : ℤ) (ε : Fin 2) (K : ParityWindow a ε → Set α) :
    ∀ R ∈ labeledResidualFamily M U κ F a ε K, R ⊆ U := by
  rintro R hR e he
  obtain ⟨S, hS, rfl⟩ := Finset.mem_image.mp hR
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp he
  exact groupLabel_mem U i

lemma labeledResidualFamily_card (M : Matroid α) (hE : M.E = Set.univ)
    (U : Finset α) (hU : U.Nonempty) (κ : ℕ) (hκ : 2 ≤ κ)
    (F : ℤ → Set α) (a : ℤ) (ε : Fin 2) (K : ParityWindow a ε → Set α) :
    ((labeledResidualFamily M U κ F a ε K).card : ℝ) ≤
      Real.exp (1000 * Real.log (κ : ℝ) / (κ : ℝ) * U.card) := by
  obtain ⟨d, hd⟩ := hU
  have hc : (labeledResidualFamily M U κ F a ε K).card ≤
      (integerResidualFamily M U (U.card / κ) F a ε K (groupLabel U)).card := Finset.card_image_le
  exact (show ((labeledResidualFamily M U κ F a ε K).card : ℝ) ≤
    (integerResidualFamily M U (U.card / κ) F a ε K (groupLabel U)).card by exact_mod_cast hc).trans
      (integerResidualFamily_card_le_exp M hE d U κ hκ F a ε K (groupLabel U) rfl)

noncomputable def nominalResidualSet (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D C T : ℕ → Set α) (h : ℕ) (U : Set α) (ε : Fin 2)
    (W : ParityWindow (activation h) ε → Set α) : Set α :=
  ⋃ b, nominalLayerSet M hE κ D C h U ε b \
    M.closure ((nominalPath M hE κ D C h (b.val.val - 2) ∪
      lowerCompetition M hE κ D C T b.val.val h) ∪ W b)

lemma nominalResidualSet_subset
    {α : Type u_1} [Fintype α] [LinearOrder α] (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D C T : ℕ → Set α) (h : ℕ) (U : Set α) (ε : Fin 2)
    (W : ParityWindow (activation h) ε → Set α) :
    nominalResidualSet M hE κ D C T h U ε W ⊆ U := by
  intro e he
  obtain ⟨b, hb⟩ := Set.mem_iUnion.mp he
  exact hb.1.1

lemma nominalResidualSet_eq_labeled (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D C T : ℕ → Set α) (h : ℕ) (U Z : Finset α) (ε : Fin 2)
    (W : ParityWindow (activation h) ε → Set α) (β : Z → ParityWindow (activation h) ε)
    (hβ : ∀ b, (fun w : Z => w.val) '' {w | β w = b} = W b) :
    (integerResidual M (nominalPath M hE κ D C h) (groupLabel U) (activation h) ε
      (fun b => lowerCompetition M hE κ D C T b.val.val h) (fun w : Z => w.val) β).image (groupLabel U) =
        (Set.toFinite (nominalResidualSet M hE κ D C T h (U : Set α) ε W)).toFinset := by
  classical
  ext e
  simp only [Finset.mem_image, Set.Finite.mem_toFinset]
  constructor
  · rintro ⟨i, hi, rfl⟩
    obtain ⟨b, hb, hn⟩ := (Finset.mem_filter.mp hi).2
    have hl := (Finset.mem_filter.mp hb).2
    apply Set.mem_iUnion.mpr
    refine ⟨b, ?_, ?_⟩
    · exact ⟨groupLabel_mem U i, hl⟩
    · simpa only [hβ b] using hn
  · intro he
    obtain ⟨b, hb, hn⟩ := Set.mem_iUnion.mp he
    obtain ⟨i, hi⟩ := exists_groupLabel U hb.1
    refine ⟨i, ?_, hi⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, b, ?_, ?_⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simpa only [hi] using hb.2⟩
    · simpa only [hi, hβ b] using hn

end MatroidProphet

end OAI
