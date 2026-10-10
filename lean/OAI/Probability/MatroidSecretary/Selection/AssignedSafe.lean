import OAI.Probability.MatroidProphet.Main
import OAI.Probability.MatroidSecretary.Selection.SafeSpecification

namespace OAI

namespace MatroidProphet

open Finset
variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The stronger half-loss estimate explicitly obtained in the source proof.
The named lemma then enlarges the loss from `|D_h|/(2κ)` to `|D_h|/κ`. -/
theorem safeSampleCount_half_loss
    (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (hκ : 0 < κ) (D : ℕ → Set α) (G : ℕ → Finset α)
    (hG : Pairwise (fun i j => Disjoint (G i) (G j)))
    (q : α → ℝ) (hq0 : ∀ e, 0 ≤ q e) (hq1 : ∀ e, q e ≤ 1)
    (h : ℕ) (I : Finset α) (hI : M.Indep (I : Set α)) :
    (((2 : ℝ) ^ 12)⁻¹) / 4 * I.card - (D h).ncard / (2 * (κ : ℝ)) ≤
      bitsExpectation q univ (fun C => bitsExpectation q univ (fun T =>
        fairParityExpectation (safeSampleCount M hE κ D G h I C T))) := by
  have hpre := safeCountBeforeParity_lower M hE κ hκ D G hG q hq0 hq1 h I hI
  have heq : bitsExpectation q univ (fun C => bitsExpectation q univ (fun T =>
      fairParityExpectation (safeSampleCount M hE κ D G h I C T))) =
      bitsExpectation q univ (fun C =>
        bitsExpectation q univ (safeCountBeforeParity M hE κ D G h I C)) / 2 := by
    simp only [safeSampleCount_fair_parity, div_eq_mul_inv]
    simp_rw [bitsExpectation_mul_right]
  rw [heq]
  have hloss : ((D h).ncard : ℝ) / (2 * (κ : ℝ)) =
      ((D h).ncard : ℝ) / (κ : ℝ) / 2 := by ring
  rw [hloss]
  linarith

end MatroidProphet

namespace MatroidProphet.MainAlgorithm

open Finset
variable {n : ℕ}
attribute [local instance] Classical.propDecidable

/-- The fixed-density safety estimate with the exact density-sample loss. -/
theorem listedSafeStatistic_exact_density
    (M : Matroid (Fin n)) (hE : M.E = Set.univ)
    (κ : ℕ) (hκ : 0 < κ) (d : MainMasks n) (s : Fin n → Option ℤ) (i : ℤ)
    (Y : Set (Fin n)) (hY : Y ⊆ (trueGroup M d s i : Set (Fin n)))
    (hI : M.Indep Y) (q : Fin n → ℝ)
    (hq0 : ∀ e, 0 ≤ q e) (hq1 : ∀ e, q e ≤ 1) :
    exitThreshold / 4 * ((d.D : Set (Fin n)) ∩ Y).ncard -
        (d.D ∩ trueGroup M d s i).card / (κ : ℝ) ≤
      bitsExpectation q univ (fun C => bitsExpectation q univ (fun T =>
        fairParityExpectation (fun p =>
          (listedSafeStatistic M hE κ (withMasks d d.D C T) s i Y
            (boolParity p) : ℝ)))) := by
  by_cases hi : i ∈ groups M d s
  · have hsafe := safeLayerStatistic_lower M hE κ hκ (groupMask M d s d.D)
      (groupGround M d s) (groupGround_disjoint M d s) q hq0 hq1
      ((groups M d s).idxOf i) (trueGroup M d s i : Set (Fin n))
      ((d.D : Set (Fin n)) ∩ Y) (Set.inter_subset_right.trans hY)
      (hI.subset Set.inter_subset_right)
    rw [groupMask_at_key M d s d.D _ i (groups_get?_idxOf M d s i hi),
      Set.ncard_coe_finset] at hsafe
    simpa only [listedSafeStatistic_guards M hE κ d s i Y,
      hi, exitThreshold] using hsafe
  · have hempty := unlisted_density_inter_empty M d s i hi Y hY
    have hzero (C T : Finset (Fin n)) (p : Bool) :
        listedSafeStatistic M hE κ (withMasks d d.D C T) s i Y
          (boolParity p) = 0 := by
      change (if i ∈ groups M d s then _ else 0) = 0
      rw [ite_eq_right hi]
    simp only [hempty, Set.ncard_empty, Nat.cast_zero, mul_zero, zero_sub,
      hzero, fairParityExpectation, zero_add, zero_div, bitsExpectation_const]
    exact neg_nonpos.mpr (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))

/-- Restricting the comparison set to this true group does not change its
safe-label statistic. This permits the source's global independent set `Y`. -/
theorem listedSafeStatistic_inter_trueGroup
    (M : Matroid (Fin n)) (hE : M.E = Set.univ) (κ : ℕ)
    (d : MainMasks n) (s : Fin n → Option ℤ) (i : ℤ)
    (Y : Set (Fin n)) (ε : Fin 2) :
    listedSafeStatistic M hE κ d s i
      (Y ∩ (trueGroup M d s i : Set (Fin n))) ε =
      listedSafeStatistic M hE κ d s i Y ε := by
  unfold listedSafeStatistic
  split_ifs
  · unfold safeLayerStatistic
    apply sum_congr rfl
    intro b _
    congr 1
    ext e
    simp only [safeLayerSet, Set.mem_sdiff, Set.mem_inter_iff]
    constructor
    · rintro ⟨⟨⟨heD, heY, _⟩, heL⟩, heN⟩
      exact ⟨⟨⟨heD, heY⟩, heL⟩, heN⟩
    · rintro ⟨⟨⟨heD, heY⟩, heL⟩, heN⟩
      exact ⟨⟨⟨heD, heY, heL.1⟩, heL⟩, heN⟩
  · rfl

/-- Source `lem:safe`, specialized to the manuscript's literal density
threshold and thinning rate, for the global independent comparison set.
It also covers an unlisted group, whose safe count is defined to be zero. -/
theorem safe_sampled_labels
    (M : Matroid (Fin n)) (hE : M.E = Set.univ)
    (d : MainMasks n) (s : Fin n → Option ℤ) (i : ℤ)
    (Y : Set (Fin n)) (hI : M.Indep Y) :
    exitThreshold / 4 *
        ((d.D : Set (Fin n)) ∩ (Y ∩ (trueGroup M d s i : Set (Fin n)))).ncard -
        (d.D ∩ trueGroup M d s i).card / densityThreshold ≤
      bitsExpectation (fun _ => thinningRate) univ (fun C =>
        bitsExpectation (fun _ => thinningRate) univ (fun T =>
          fairParityExpectation (fun p =>
            (listedSafeStatistic M hE (2 ^ 100) (withMasks d d.D C T) s i Y
              (boolParity p) : ℝ)))) := by
  have hs := listedSafeStatistic_exact_density M hE (2 ^ 100) (by positivity)
    d s i (Y ∩ (trueGroup M d s i : Set (Fin n))) Set.inter_subset_right
    (hI.subset Set.inter_subset_left) (fun _ => thinningRate)
    (fun _ => constants_positive.2.2.1.le)
    (fun _ => by norm_num [thinningRate])
  have heq (C T : Finset (Fin n)) (p : Bool) :
      listedSafeStatistic M hE (2 ^ 100) (withMasks d d.D C T) s i
        (Y ∩ (trueGroup M d s i : Set (Fin n))) (boolParity p) =
      listedSafeStatistic M hE (2 ^ 100) (withMasks d d.D C T) s i Y
        (boolParity p) := by
    simpa only [trueGroup_withMasks] using
      listedSafeStatistic_inter_trueGroup M hE (2 ^ 100)
        (withMasks d d.D C T) s i Y (boolParity p)
  simpa only [Nat.cast_pow, Nat.cast_ofNat, densityThreshold, heq] using hs

/-- Proof of the independently stated complete safe-label claim. -/
theorem safe_sampled_labels_claim : SafeSampleClaim := by
  intro n M hE d s i Y hI
  exact safe_sampled_labels M hE d s i Y hI

end MatroidProphet.MainAlgorithm

end OAI
