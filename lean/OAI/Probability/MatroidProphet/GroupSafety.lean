import OAI.Probability.MatroidProphet.GroupConditioning
import OAI.Probability.MatroidProphet.SafeStatistics
import OAI.Probability.MatroidProphet.Constants

namespace OAI

namespace MatroidProphet.MainAlgorithm
open Finset
variable {n : ℕ}
attribute [local instance] Classical.propDecidable

noncomputable def groupGround (M : Matroid (Fin n)) (d : MainMasks n)
    (s : Fin n → Option ℤ) (j : ℕ) : Finset (Fin n) :=
  (groupMask M d s univ j).toFinset

lemma mem_groupGround (M : Matroid (Fin n)) (d : MainMasks n)
    (s : Fin n → Option ℤ) (j : ℕ) (e : Fin n) :
    e ∈ groupGround M d s j ↔ candidate M d s e (s e) ∧ s e = (groups M d s)[j]? := by
  rw [groupGround, Set.mem_toFinset]
  simp [groupMask]

lemma groupGround_disjoint (M : Matroid (Fin n)) (d : MainMasks n)
    (s : Fin n → Option ℤ) : Pairwise (fun i j => Disjoint (groupGround M d s i) (groupGround M d s j)) := by
  intro i j hij
  apply disjoint_left.mpr
  intro e hei hej
  obtain ⟨hc, hei⟩ := (mem_groupGround M d s i e).mp hei
  obtain ⟨_, hej⟩ := (mem_groupGround M d s j e).mp hej
  have hi : i < (groups M d s).length := by
    by_contra hi
    exact hc.1 (hei.trans (List.getElem?_eq_none (by omega)))
  exact hij ((List.Nodup.getElem?_inj hi (groups_nodup M d s)).mp (hei.symm.trans hej))

lemma groupMask_eq_inter_ground (M : Matroid (Fin n)) (d : MainMasks n)
    (s : Fin n → Option ℤ) (A : Finset (Fin n)) (j : ℕ) :
    groupMask M d s A j = (A : Set (Fin n)) ∩ (groupGround M d s j : Set (Fin n)) := by
  ext e
  simp only [groupMask, Set.mem_ofPred_eq, Set.mem_inter_iff, Finset.mem_coe, mem_groupGround]

lemma listedSafeStatistic_guards (M : Matroid (Fin n)) (hE : M.E = Set.univ)
    (κ : ℕ) (d : MainMasks n) (s : Fin n → Option ℤ) (i : ℤ)
    (Y : Set (Fin n)) (ε : Fin 2) (C T : Finset (Fin n))
    (hi : i ∈ groups M d s) :
    listedSafeStatistic M hE κ (withMasks d d.D C T) s i Y ε =
      safeLayerStatistic M hE κ (groupMask M d s d.D)
        (fun j => (C : Set (Fin n)) ∩ (groupGround M d s j : Set (Fin n)))
        (fun j => (T : Set (Fin n)) ∩ (groupGround M d s j : Set (Fin n)))
        ((groups M d s).idxOf i) (trueGroup M d s i : Set (Fin n))
        ((d.D : Set (Fin n)) ∩ Y) ε := by
  change (if i ∈ groups M d s then _ else _) = _
  rw [ite_eq_left hi]
  change safeLayerStatistic M hE κ (groupMask M d s d.D)
    (groupMask M d s C) (groupMask M d s T) ((groups M d s).idxOf i)
    (trueGroup M d s i : Set (Fin n)) ((d.D : Set (Fin n)) ∩ Y) ε = _
  congr 1
  · funext j
    exact groupMask_eq_inter_ground M d s C j
  · funext j
    exact groupMask_eq_inter_ground M d s T j

lemma unlisted_density_inter_empty (M : Matroid (Fin n)) (d : MainMasks n)
    (s : Fin n → Option ℤ) (i : ℤ) (hi : i ∉ groups M d s)
    (Y : Set (Fin n)) (hY : Y ⊆ (trueGroup M d s i : Set (Fin n))) :
    (d.D : Set (Fin n)) ∩ Y = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  rintro e ⟨heD, heY⟩
  exact hi ((mem_groups M d s i).mpr ((mem_listed_iff M d s i).mpr ⟨e, heD, hY heY⟩))

theorem listedSafeStatistic_fixed_density (M : Matroid (Fin n)) (hE : M.E = Set.univ)
    (κ : ℕ) (hκ : 0 < κ) (d : MainMasks n) (s : Fin n → Option ℤ) (i : ℤ)
    (Y : Set (Fin n)) (hY : Y ⊆ (trueGroup M d s i : Set (Fin n))) (hI : M.Indep Y)
    (q : Fin n → ℝ) (hq0 : ∀ e, 0 ≤ q e) (hq1 : ∀ e, q e ≤ 1) :
    (((2:ℝ)^12)⁻¹) / 4 * ((d.D : Set (Fin n)) ∩ Y).ncard -
        (trueGroup M d s i).card / (κ:ℝ) ≤
      bitsExpectation q univ (fun C => bitsExpectation q univ (fun T =>
        fairParityExpectation (fun p =>
          (listedSafeStatistic M hE κ (withMasks d d.D C T) s i Y (boolParity p) : ℝ)))) := by
  by_cases hi : i ∈ groups M d s
  · have hsafe := safeLayerStatistic_lower M hE κ hκ (groupMask M d s d.D)
      (groupGround M d s) (groupGround_disjoint M d s) q hq0 hq1
      ((groups M d s).idxOf i) (trueGroup M d s i : Set (Fin n))
      ((d.D : Set (Fin n)) ∩ Y) (Set.inter_subset_right.trans hY) (hI.subset Set.inter_subset_right)
    have hcard : (groupMask M d s d.D ((groups M d s).idxOf i)).ncard ≤ (trueGroup M d s i).card := by
      rw [groupMask_at_key M d s d.D _ i (groups_get?_idxOf M d s i hi), Set.ncard_coe_finset]
      exact card_le_card inter_subset_right
    have hdiv : ((groupMask M d s d.D ((groups M d s).idxOf i)).ncard : ℝ) / (κ:ℝ) ≤
        (trueGroup M d s i).card / (κ:ℝ) :=
      div_le_div_of_nonneg_right (by exact_mod_cast hcard) (Nat.cast_nonneg κ)
    have heq : bitsExpectation q univ (fun C => bitsExpectation q univ (fun T =>
        fairParityExpectation (fun p =>
          (listedSafeStatistic M hE κ (withMasks d d.D C T) s i Y (boolParity p) : ℝ)))) =
        bitsExpectation q univ (fun C => bitsExpectation q univ (fun T =>
          fairParityExpectation (fun p => (safeLayerStatistic M hE κ (groupMask M d s d.D)
            (fun j => (C : Set (Fin n)) ∩ (groupGround M d s j : Set (Fin n)))
            (fun j => (T : Set (Fin n)) ∩ (groupGround M d s j : Set (Fin n)))
            ((groups M d s).idxOf i) (trueGroup M d s i : Set (Fin n))
            ((d.D : Set (Fin n)) ∩ Y) (boolParity p) : ℝ)))) := by
      apply bitsExpectation_congr
      intro C hC
      apply bitsExpectation_congr
      intro T hT
      congr 1
      funext p
      rw [listedSafeStatistic_guards M hE κ d s i Y (boolParity p) C T hi]
    rw [heq]
    exact (sub_le_sub_left hdiv _).trans hsafe
  · have hempty := unlisted_density_inter_empty M d s i hi Y hY
    have hzero (C T : Finset (Fin n)) (p : Bool) :
        listedSafeStatistic M hE κ (withMasks d d.D C T) s i Y (boolParity p) = 0 := by
      change (if i ∈ groups M d s then _ else 0) = 0
      rw [ite_eq_right hi]
    simp only [hempty, Set.ncard_empty, Nat.cast_zero, mul_zero, zero_sub, hzero,
      fairParityExpectation, zero_add, zero_div, bitsExpectation_const]
    exact neg_nonpos.mpr (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))

theorem listedSafeStatistic_lower (M : Matroid (Fin n)) (hE : M.E = Set.univ)
    (κ : ℕ) (hκ : 0 < κ) (d : MainMasks n) (s : Fin n → Option ℤ) (i : ℤ)
    (Y : Set (Fin n)) (hY : Y ⊆ (trueGroup M d s i : Set (Fin n))) (hI : M.Indep Y)
    (q : Fin n → ℝ) (hq0 : ∀ e, 0 ≤ q e) (hq1 : ∀ e, q e ≤ 1) :
    retainedFraction * Y.ncard - (trueGroup M d s i).card / (κ:ℝ) ≤
      tripleMaskExpectation (fun _ => (1:ℝ)/4) q q univ (fun D C T =>
        fairParityExpectation (fun p =>
          (listedSafeStatistic M hE κ (withMasks d D C T) s i Y (boolParity p) : ℝ))) := by
  have hfixed (D : Finset (Fin n)) :
      (((2:ℝ)^12)⁻¹) / 4 * ((D : Set (Fin n)) ∩ Y).ncard -
          (trueGroup M d s i).card / (κ:ℝ) ≤
        bitsExpectation q univ (fun C => bitsExpectation q univ (fun T =>
          fairParityExpectation (fun p =>
            (listedSafeStatistic M hE κ (withMasks d D C T) s i Y (boolParity p) : ℝ)))) :=
    listedSafeStatistic_fixed_density M hE κ hκ (withMasks d D ∅ ∅) s i Y hY hI q hq0 hq1
  have hmean := bitsExpectation_mono (fun _ : Fin n => (1:ℝ)/4) (by intro e; norm_num)
    (by intro e; norm_num) univ (fun D _ => hfixed D)
  have hcard : bitsExpectation (fun _ : Fin n => (1:ℝ)/4) univ
      (fun D => (((D : Set (Fin n)) ∩ Y).ncard : ℝ)) = Y.ncard / 4 := by
    have hset (D : Finset (Fin n)) : (D : Set (Fin n)) ∩ Y =
        ((Y.toFinset ∩ D : Finset (Fin n)) : Set (Fin n)) := by
      ext e
      simp only [Set.mem_inter_iff, Finset.mem_coe, mem_inter, Set.mem_toFinset]
      exact and_comm
    simp only [hset, Set.ncard_coe_finset]
    rw [bitsExpectation_card_inter (fun _ : Fin n => (1:ℝ)/4) univ Y.toFinset (subset_univ _)]
    simp only [sum_const, nsmul_eq_mul, ← Set.ncard_eq_toFinset_card']
    ring
  have hnum : (((2:ℝ)^12)⁻¹) / 4 / 4 = retainedFraction := by
    norm_num [retainedFraction]
  have heq : bitsExpectation (fun _ : Fin n => (1:ℝ)/4) univ
      (fun D => (((2:ℝ)^12)⁻¹) / 4 * ((D : Set (Fin n)) ∩ Y).ncard -
        (trueGroup M d s i).card / (κ:ℝ)) =
      retainedFraction * Y.ncard - (trueGroup M d s i).card / (κ:ℝ) := by
    simp only [sub_eq_add_neg, bitsExpectation_add, bitsExpectation_mul_const,
      bitsExpectation_const, hcard]
    congr 1
    calc
      (((2:ℝ)^12)⁻¹) / 4 * (Y.ncard / 4) =
        ((((2:ℝ)^12)⁻¹) / 4 / 4) * Y.ncard := by ring
      _ = retainedFraction * Y.ncard := by rw [hnum]
  rw [heq] at hmean
  exact hmean

end MatroidProphet.MainAlgorithm

end OAI
