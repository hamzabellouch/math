import OAI.Probability.MatroidProphet.Residual.Deterministic

namespace OAI

namespace MatroidProphet
open Set Finset Pivots
variable {α : Type*} [Fintype α] [LinearOrder α]

lemma safeLayerStatistic_le_ncard
    {α : Type u_1} [Fintype α] [LinearOrder α] (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D C T : ℕ → Set α) (h : ℕ) (U I : Set α) (ε : Fin 2) :
    safeLayerStatistic M hE κ D C T h U I ε ≤ U.ncard := by
  let L := safeLayerSet M hE κ D C T h U I ε
  have hd : Pairwise (fun b c => Disjoint (L b) (L c)) := by
    intro b c hbc
    exact (nominalLayerSet_disjoint M hE κ D C h U ε hbc).mono
      (fun _ he => he.1.2) (fun _ he => he.1.2)
  have heq : (⋃ b, L b).ncard = ∑ b, (L b).ncard := by
    simpa only [finsum_eq_sum_of_fintype] using
      Set.ncard_iUnion_of_finite (fun b => Set.toFinite (L b)) hd
  rw [show safeLayerStatistic M hE κ D C T h U I ε = ∑ b, (L b).ncard from rfl, ← heq]
  apply Set.ncard_le_ncard _ (Set.toFinite U)
  intro e he
  obtain ⟨b, hb⟩ := Set.mem_iUnion.mp he
  exact hb.1.2.1

noncomputable def nominalTransferGap (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D C T : ℕ → Set α) (h : ℕ) (U O I : Set α) (ε : Fin 2) : ℝ :=
  max ((safeLayerStatistic M hE κ D C T h U I ε : ℝ) -
    (κ : ℝ) * nominalRankStatistic M hE κ D C T h U O ε) 0

lemma safe_le_rank_add_gap
    {α : Type u_1} [Fintype α] [LinearOrder α] (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D C T : ℕ → Set α) (h : ℕ) (U O I : Set α) (ε : Fin 2) :
    (safeLayerStatistic M hE κ D C T h U I ε : ℝ) ≤
      (κ : ℝ) * nominalRankStatistic M hE κ D C T h U O ε +
        nominalTransferGap M hE κ D C T h U O I ε := by
  have hx := le_max_left ((safeLayerStatistic M hE κ D C T h U I ε : ℝ) -
    (κ : ℝ) * nominalRankStatistic M hE κ D C T h U O ε) 0
  unfold nominalTransferGap
  linarith

lemma nominalTransferGap_le_bad (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (hκ : 0 < κ) (D C T : ℕ → Set α) (h : ℕ) (U S : Finset α) (O I : Set α)
    (hDU : D h ⊆ (U : Set α)) (hI : I ⊆ D h) (hS : S ⊆ U)
    (hOS : O ∩ (U : Set α) ⊆ (S : Set α))
    (hnonloop : ∀ e ∈ U, e ∉ M.closure ∅) (ε : Fin 2) :
    nominalTransferGap M hE κ D C T h (U : Set α) O I ε ≤
      residualDelta * U.card + (U.card : ℝ) * residualBadIndicator
        (labeledResidualFamily M U κ (guardedPath M hE κ D C h) (activation h) ε
          (fun b => lowerCompetition M hE κ D C T b.val.val h))
        (residualDelta * U.card) S := by
  classical
  let F := labeledResidualFamily M U κ (guardedPath M hE κ D C h) (activation h) ε
    (fun b => lowerCompetition M hE κ D C T b.val.val h)
  have hn : 0 ≤ residualDelta * (U.card : ℝ) + (U.card : ℝ) *
      residualBadIndicator F (residualDelta * U.card) S := by
    apply add_nonneg (mul_nonneg residualDelta_nonneg (Nat.cast_nonneg _))
    apply mul_nonneg (Nat.cast_nonneg _)
    unfold residualBadIndicator
    split_ifs <;> norm_num
  by_cases hz : nominalRankStatistic M hE κ D C T h (U : Set α) O ε ≤ U.card / κ
  · obtain ⟨R, hR, hRO, hdet⟩ := exists_captured_residual M hE κ hκ D C T h U O I
      hDU hI hnonloop ε hz
    have hRU : R ⊆ U := labeledResidualFamily_subsets M U κ _ _ ε _ R hR
    have hRS : R ⊆ S := fun e he => hOS ⟨hRO he, hRU he⟩
    have hcap := capturedResidual_le U S R F hS hR hRS
    have hdet' : (safeLayerStatistic M hE κ D C T h (U : Set α) I ε : ℝ) ≤
        (κ : ℝ) * nominalRankStatistic M hE κ D C T h (U : Set α) O ε + R.card := by
      exact_mod_cast hdet
    exact max_le (by linarith) hn
  · have hnz : U.card < κ * nominalRankStatistic M hE κ D C T h (U : Set α) O ε := by
      have hz' := Nat.div_lt_iff_lt_mul hκ |>.mp (lt_of_not_ge hz)
      simpa only [Nat.mul_comm] using hz'
    have hs := safeLayerStatistic_le_ncard M hE κ D C T h (U : Set α) I ε
    rw [Set.ncard_coe_finset] at hs
    have hsz : (safeLayerStatistic M hE κ D C T h (U : Set α) I ε : ℝ) ≤
        (κ : ℝ) * nominalRankStatistic M hE κ D C T h (U : Set α) O ε := by
      exact_mod_cast hs.trans hnz.le
    exact max_le (by linarith) hn

end MatroidProphet

end OAI
