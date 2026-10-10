import OAI.Probability.MatroidProphet.Residual.LabeledFamily
import OAI.Probability.MatroidProphet.PathRankCost

namespace OAI

namespace MatroidProphet
open Set Finset Pivots
variable {α : Type*} [Fintype α] [LinearOrder α]

lemma safeLayer_le_witness_residual
    {α : Type u_1} [Fintype α] [LinearOrder α] (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D C T : ℕ → Set α) (h : ℕ) (U I : Set α) (hI : I ⊆ D h)
    (ε : Fin 2) (b : ParityWindow (activation h) ε) (W : Set α) :
    (safeLayerSet M hE κ D C T h U I ε b).ncard ≤ κ * W.ncard +
      (nominalLayerSet M hE κ D C h U ε b \
        M.closure (nominalPath M hE κ D C h (b.val.val - 2) ∪
          lowerCompetition M hE κ D C T b.val.val h ∪ W)).ncard := by
  by_cases hv : activation h + 2 ≤ b.val.val ∧ b.val.val ≤ 0
  · have hx : nominalPath M hE κ D C h (b.val.val - 2) =
        densityExpansion M hE κ (D h) (guardedPath M hE κ D C h (b.val.val - 2)) := by
      unfold nominalPath densityEnabled
      rw [ite_eq_left (by omega)]
    rw [hx]
    apply safe_layer_le_witness_residual M hE κ (D h)
      (guardedPath M hE κ D C h (b.val.val - 2)) (lowerCompetition M hE κ D C T b.val.val h)
      W (nominalLayerSet M hE κ D C h U ε b) (safeLayerSet M hE κ D C T h U I ε b)
    intro e he
    exact ⟨⟨hI he.1.1, he.1.2⟩, he.2⟩
  · have he : nominalLayerSet M hE κ D C h U ε b = ∅ := by
      ext e
      constructor
      · exact fun he => (hv ⟨he.2.1, he.2.2.1⟩).elim
      · simp
    simp [safeLayerSet, he]

lemma safeStatistic_le_witness_residual (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D C T : ℕ → Set α) (h : ℕ) (U I : Set α) (hI : I ⊆ D h)
    (ε : Fin 2) (W : ParityWindow (activation h) ε → Set α) :
    safeLayerStatistic M hE κ D C T h U I ε ≤ κ * (∑ b, (W b).ncard) +
      (nominalResidualSet M hE κ D C T h U ε W).ncard := by
  unfold safeLayerStatistic
  calc
    _ ≤ ∑ b, (κ * (W b).ncard +
        (nominalLayerSet M hE κ D C h U ε b \
          M.closure ((nominalPath M hE κ D C h (b.val.val - 2) ∪
            lowerCompetition M hE κ D C T b.val.val h) ∪ W b)).ncard) :=
      sum_le_sum (fun b _ => safeLayer_le_witness_residual M hE κ D C T h U I hI ε b (W b))
    _ = _ := by
      rw [sum_add_distrib, ← mul_sum, ← residualUnion_ncard M _ _ W
        (nominalLayerSet_disjoint M hE κ D C h U ε)]
      rfl

lemma exists_captured_residual (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (hκ : 0 < κ) (D C T : ℕ → Set α) (h : ℕ) (U : Finset α) (O I : Set α)
    (hDU : D h ⊆ (U : Set α)) (hI : I ⊆ D h)
    (hnonloop : ∀ e ∈ U, e ∉ M.closure ∅) (ε : Fin 2)
    (hzsmall : nominalRankStatistic M hE κ D C T h (U : Set α) O ε ≤ U.card / κ) :
    ∃ R ∈ labeledResidualFamily M U κ (guardedPath M hE κ D C h) (activation h) ε
        (fun b => lowerCompetition M hE κ D C T b.val.val h),
      (R : Set α) ⊆ O ∧ safeLayerStatistic M hE κ D C T h (U : Set α) I ε ≤
        κ * nominalRankStatistic M hE κ D C T h (U : Set α) O ε + R.card := by
  classical
  obtain ⟨W, hW, hsum, hspan, Z, hZU, hZcard, β, hβ⟩ :=
    nominal_rank_witnesses M hE κ D C T h U O ε
  let R := (Set.toFinite (nominalResidualSet M hE κ D C T h (U : Set α) ε W)).toFinset
  have hmask : (R : Set α) ⊆ O := by
    intro e he
    exact residualUnion_subset_mask M _ _ W O hspan ((Set.Finite.mem_toFinset _).mp he)
  have hdet : safeLayerStatistic M hE κ D C T h (U : Set α) I ε ≤
      κ * nominalRankStatistic M hE κ D C T h (U : Set α) O ε + R.card := by
    have h := safeStatistic_le_witness_residual M hE κ D C T h (U : Set α) I hI ε W
    rwa [hsum, Set.ncard_eq_toFinset_card] at h
  refine ⟨R, ?_, hmask, hdet⟩
  apply Finset.mem_image.mpr
  refine ⟨integerResidual M (nominalPath M hE κ D C h) (groupLabel U) (activation h) ε
      (fun b => lowerCompetition M hE κ D C T b.val.val h) (fun w : Z => w.val) β, ?_, ?_⟩
  · apply nominal_residual_mem_family M hE κ hκ D C h U Z hDU hZU (hZcard.trans hzsmall) ε
      (fun b => lowerCompetition M hE κ D C T b.val.val h)
      (fun b => lowerCompetition_subset_guarded M hE κ D C T b.val.val h) β
    · intro w
      have hw : w.val ∈ W (β w) := by
        rw [← hβ (β w)]
        exact ⟨w, rfl, rfl⟩
      exact (hW (β w) hw).1.2.2.2.1
    · exact fun i => hnonloop _ (groupLabel_mem U i)
  · exact nominalResidualSet_eq_labeled M hE κ D C T h U Z ε W β hβ

end MatroidProphet

end OAI
