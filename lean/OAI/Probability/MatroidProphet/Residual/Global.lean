import OAI.Probability.MatroidProphet.FocalTransfer

namespace OAI

namespace MatroidProphet
open Finset
variable {α : Type*} [DecidableEq α]

lemma tripleMaskExpectation_split (p q r : α → ℝ) (V U : Finset α) (hU : U ⊆ V)
    (f : Finset α → Finset α → Finset α → ℝ) :
    tripleMaskExpectation p q r V f =
      tripleMaskExpectation p q r (V \ U) (fun D C T =>
        tripleMaskExpectation p q r U (fun A B X => f (D ∪ A) (C ∪ B) (T ∪ X))) := by
  unfold tripleMaskExpectation
  rw [bitsExpectation_split p V U hU]
  apply bitsExpectation_congr
  intro D hD
  simp_rw [bitsExpectation_split q V U hU]
  rw [bitsExpectation_comm p q U (V \ U)]
  apply bitsExpectation_congr
  intro C hC
  simp_rw [bitsExpectation_split r V U hU]
  simp_rw [bitsExpectation_comm q r U (V \ U)]
  rw [bitsExpectation_comm p r U (V \ U)]

lemma tripleMaskExpectation_const (p q r : α → ℝ) (V : Finset α) (c : ℝ) :
    tripleMaskExpectation p q r V (fun _ _ _ => c) = c := by
  simp only [tripleMaskExpectation, bitsExpectation_const]

lemma tripleMaskExpectation_congr (p q r : α → ℝ) (V : Finset α)
    {f g : Finset α → Finset α → Finset α → ℝ}
    (h : ∀ D ⊆ V, ∀ C ⊆ V, ∀ T ⊆ V, f D C T = g D C T) :
    tripleMaskExpectation p q r V f = tripleMaskExpectation p q r V g := by
  apply bitsExpectation_congr
  intro D hD
  apply bitsExpectation_congr
  intro C hC
  exact bitsExpectation_congr r V (fun T hT => h D hD C hC T hT)

namespace MainAlgorithm
variable {n : ℕ}

lemma focalMasks_withMasks (d : MainMasks n) (U D C T A B X : Finset (Fin n))
    (hD : D ⊆ univ \ U) (hC : C ⊆ univ \ U) (hT : T ⊆ univ \ U) :
    focalMasks (withMasks d D C T) U A B X = withMasks d (D ∪ A) (C ∪ B) (T ∪ X) := by
  have hD' : D \ U = D := by ext e; simp only [mem_sdiff]; exact ⟨And.left, fun he => ⟨he, (mem_sdiff.mp (hD he)).2⟩⟩
  have hC' : C \ U = C := by ext e; simp only [mem_sdiff]; exact ⟨And.left, fun he => ⟨he, (mem_sdiff.mp (hC he)).2⟩⟩
  have hT' : T \ U = T := by ext e; simp only [mem_sdiff]; exact ⟨And.left, fun he => ⟨he, (mem_sdiff.mp (hT he)).2⟩⟩
  simp only [focalMasks, withMasks, hD', hC', hT']

lemma listedTransferGap_expectation_le (M : Matroid (Fin n)) (hE : M.E = Set.univ)
    (d : MainMasks n) (s : Fin n → Option ℤ) (i : ℤ) (Y : Set (Fin n))
    (hY : Y ⊆ (trueGroup M d s i : Set (Fin n)))
    (hn : densityThreshold ≤ ((trueGroup M d s i).card : ℝ)) (ε : Fin 2) :
    tripleMaskExpectation (fun _ => (1:ℝ)/4) (fun _ => thinningRate) (fun _ => thinningRate)
      univ (fun A B C => listedTransferGap M hE (2^100) (withMasks d A B C) s i Y ε) ≤
      2 * residualDelta * (trueGroup M d s i).card := by
  rw [tripleMaskExpectation_split _ _ _ univ (trueGroup M d s i) (subset_univ _)]
  have ht0 : 0 ≤ thinningRate := constants_positive.2.2.1.le
  have ht1 : thinningRate ≤ 1 := by norm_num [thinningRate]
  calc
    _ ≤ tripleMaskExpectation (fun _ => (1:ℝ)/4) (fun _ => thinningRate) (fun _ => thinningRate)
        (univ \ trueGroup M d s i) (fun _ _ _ => 2 * residualDelta * (trueGroup M d s i).card) := by
      apply tripleMaskExpectation_mono _ _ _ (fun _ => by norm_num) (fun _ => by norm_num)
        (fun _ => ht0) (fun _ => ht1) (fun _ => ht0) (fun _ => ht1)
      intro D hD C hC T hT
      have hh := focalTransferGap_expectation_le M hE (withMasks d D C T) s i Y hY hn ε
      apply le_trans ?_ hh
      apply le_of_eq
      apply tripleMaskExpectation_congr
      intro A hA B hB X hX
      rw [trueGroup_withMasks, focalMasks_withMasks d _ D C T A B X hD hC hT]
    _ = _ := tripleMaskExpectation_const _ _ _ _ _

lemma listedTransferGap_parity_expectation_le (M : Matroid (Fin n)) (hE : M.E = Set.univ)
    (d : MainMasks n) (s : Fin n → Option ℤ) (i : ℤ) (Y : Set (Fin n))
    (hY : Y ⊆ (trueGroup M d s i : Set (Fin n)))
    (hn : densityThreshold ≤ ((trueGroup M d s i).card : ℝ)) :
    tripleMaskExpectation (fun _ => (1:ℝ)/4) (fun _ => thinningRate) (fun _ => thinningRate)
      univ (fun A B C => fairParityExpectation (fun p =>
        listedTransferGap M hE (2^100) (withMasks d A B C) s i Y (boolParity p))) ≤
      2 * residualDelta * (trueGroup M d s i).card := by
  have h0 := listedTransferGap_expectation_le M hE d s i Y hY hn (boolParity false)
  have h1 := listedTransferGap_expectation_le M hE d s i Y hY hn (boolParity true)
  simp only [fairParityExpectation, div_eq_mul_inv, mul_comm _ ((2:ℝ)⁻¹)]
  rw [tripleMaskExpectation_mul, tripleMaskExpectation_add]
  linarith

end MainAlgorithm
end MatroidProphet

end OAI
