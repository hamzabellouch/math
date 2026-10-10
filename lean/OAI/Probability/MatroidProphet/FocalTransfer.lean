import OAI.Probability.MatroidProphet.Residual.Gap
import OAI.Probability.MatroidProphet.GroupConditioning
import OAI.Probability.MatroidProphet.SafeParity

namespace OAI

namespace MatroidProphet.MainAlgorithm
open Finset Pivots
variable {n : ℕ}

noncomputable def listedTransferGap (M : Matroid (Fin n)) (hE : M.E = Set.univ)
    (κ : ℕ) (d : MainMasks n) (s : Fin n → Option ℤ) (i : ℤ)
    (Y : Set (Fin n)) (ε : Fin 2) : ℝ :=
  max ((listedSafeStatistic M hE κ d s i Y ε : ℝ) -
    (κ : ℝ) * listedRankStatistic M hE κ d s i ε) 0

lemma trueGroup_nonloop (M : Matroid (Fin n)) (d : MainMasks n)
    (s : Fin n → Option ℤ) (i : ℤ) :
    ∀ e ∈ trueGroup M d s i, e ∉ M.closure ∅ := by
  intro e he hl
  have hc := (mem_trueGroup M d s i e).mp he
  exact hc.1.2.2 (M.closure_mono (Set.empty_subset _) hl)

noncomputable def focalResidualFamily (M : Matroid (Fin n)) (hE : M.E = Set.univ)
    (κ : ℕ) (d : MainMasks n) (s : Fin n → Option ℤ) (i : ℤ) (ε : Fin 2) :
    Finset (Finset (Fin n)) :=
  let r := focalReference M d s i
  labeledResidualFamily M (trueGroup M d s i) κ
    (guardedPath M hE κ (groupMask M r s r.D) (groupMask M r s r.C) (focalIndex M d s i))
    (activation (focalIndex M d s i)) ε
    (fun b => lowerCompetition M hE κ (groupMask M r s r.D) (groupMask M r s r.C)
      (groupMask M r s r.T) b.val.val (focalIndex M d s i))

lemma listedTransferGap_focal_le (M : Matroid (Fin n)) (hE : M.E = Set.univ)
    (κ : ℕ) (hκ : 0 < κ) (d : MainMasks n) (s : Fin n → Option ℤ) (i : ℤ)
    (Y : Set (Fin n)) (hY : Y ⊆ (trueGroup M d s i : Set (Fin n)))
    (ε : Fin 2) (A B C : Finset (Fin n))
    (hA : A ⊆ trueGroup M d s i) (hB : B ⊆ trueGroup M d s i)
    (hC : C ⊆ trueGroup M d s i) :
    listedTransferGap M hE κ (focalMasks d (trueGroup M d s i) A B C) s i Y ε ≤
      residualDelta * (trueGroup M d s i).card + ((trueGroup M d s i).card : ℝ) *
        residualBadIndicator (focalResidualFamily M hE κ d s i ε)
          (residualDelta * (trueGroup M d s i).card) (A ∪ B) := by
  classical
  by_cases hne : A.Nonempty
  · let f := focalMasks d (trueGroup M d s i) A B C
    have hg : groupMask M f s f.D (focalIndex M d s i) = (A : Set (Fin n)) :=
      focal_group_mask M d s i A B C d.D A hA hne hA
    have hDU : groupMask M f s f.D (focalIndex M d s i) ⊆ (trueGroup M d s i : Set (Fin n)) := by
      rw [hg]
      exact hA
    have hI : (f.D : Set (Fin n)) ∩ Y ⊆ groupMask M f s f.D (focalIndex M d s i) := by
      rw [hg, focal_density_inter M d s i A B C Y hY]
      exact Set.inter_subset_left
    have hOS : ((f.H ∪ f.D ∪ f.C : Finset (Fin n)) : Set (Fin n)) ∩
        (trueGroup M d s i : Set (Fin n)) ⊆ ((A ∪ B : Finset (Fin n)) : Set (Fin n)) := by
      have he := congrArg (fun X : Finset (Fin n) => (X : Set (Fin n)))
        (focal_observed_inter M d s i A B C hA hB)
      simpa only [coe_inter] using he.subset
    have h := nominalTransferGap_le_bad M hE κ hκ (groupMask M f s f.D)
      (groupMask M f s f.C) (groupMask M f s f.T) (focalIndex M d s i)
      (trueGroup M d s i) (A ∪ B) ((f.H ∪ f.D ∪ f.C : Finset (Fin n)) : Set (Fin n))
      ((f.D : Set (Fin n)) ∩ Y) hDU hI (union_subset hA hB) hOS
      (trueGroup_nonloop M d s i) ε
    have hF := funext (focal_incoming_path M hE κ d s i A B C hA hB hC hne)
    have hK := funext (fun b : ParityWindow (activation (focalIndex M d s i)) ε =>
      focal_lowerCompetition M hE κ d s i A B C hA hB hC hne b.val.val)
    rw [hF, hK] at h
    simpa only [listedTransferGap, listedSafeStatistic_focal_nonempty M hE κ d s i A B C Y ε hA hne,
      listedRankStatistic_focal_nonempty M hE κ d s i A B C ε hA hne,
      nominalTransferGap, focalResidualFamily] using h
  · have hAe : A = ∅ := not_nonempty_iff_eq_empty.mp hne
    subst A
    rw [listedTransferGap, listedSafeStatistic_focal_empty, listedRankStatistic_focal_empty]
    simp only [Nat.cast_zero, mul_zero, sub_zero, max_self]
    apply add_nonneg (mul_nonneg residualDelta_nonneg (Nat.cast_nonneg _))
    apply mul_nonneg (Nat.cast_nonneg _)
    unfold residualBadIndicator
    split_ifs <;> norm_num

lemma focalTransferGap_expectation_le (M : Matroid (Fin n)) (hE : M.E = Set.univ)
    (d : MainMasks n) (s : Fin n → Option ℤ) (i : ℤ) (Y : Set (Fin n))
    (hY : Y ⊆ (trueGroup M d s i : Set (Fin n)))
    (hn : densityThreshold ≤ ((trueGroup M d s i).card : ℝ)) (ε : Fin 2) :
    tripleMaskExpectation (fun _ => (1:ℝ)/4) (fun _ => thinningRate) (fun _ => thinningRate)
      (trueGroup M d s i) (fun A B C =>
        listedTransferGap M hE (2^100) (focalMasks d (trueGroup M d s i) A B C) s i Y ε) ≤
      2 * residualDelta * (trueGroup M d s i).card := by
  have ht0 : 0 ≤ thinningRate := constants_positive.2.2.1.le
  have ht1 : thinningRate ≤ 1 := by norm_num [thinningRate]
  have hu : (1:ℝ)/4 + (1-(1:ℝ)/4)*thinningRate ≤ 1/2 := by norm_num [thinningRate]
  have hne : (trueGroup M d s i).Nonempty := by
    apply card_pos.mp
    have hp := lt_of_lt_of_le constants_positive.2.1 hn
    exact_mod_cast hp
  apply tripleMask_residual_error_le (fun _ => (1:ℝ)/4) (fun _ => thinningRate)
    (fun _ => thinningRate) (fun _ => by norm_num) (fun _ => by norm_num)
    (fun _ => ht0) (fun _ => ht1) (fun _ => ht0) (fun _ => ht1) (fun _ => hu)
    (trueGroup M d s i) (focalResidualFamily M hE (2^100) d s i ε)
  · exact labeledResidualFamily_subsets M _ _ _ _ ε _
  · have hc := labeledResidualFamily_card M hE (trueGroup M d s i) hne (2^100)
        (by norm_num) (guardedPath M hE (2^100)
          (groupMask M (focalReference M d s i) s (focalReference M d s i).D)
          (groupMask M (focalReference M d s i) s (focalReference M d s i).C) (focalIndex M d s i))
        (activation (focalIndex M d s i)) ε
        (fun b => lowerCompetition M hE (2^100)
          (groupMask M (focalReference M d s i) s (focalReference M d s i).D)
          (groupMask M (focalReference M d s i) s (focalReference M d s i).C)
          (groupMask M (focalReference M d s i) s (focalReference M d s i).T) b.val.val (focalIndex M d s i))
    simpa only [Nat.cast_pow, Nat.cast_ofNat, densityThreshold, focalResidualFamily] using hc
  · exact hn
  · intro A hA B hB C hC
    exact listedTransferGap_focal_le M hE (2^100) (by positivity) d s i Y hY ε A B C hA hB hC

end MatroidProphet.MainAlgorithm

end OAI
