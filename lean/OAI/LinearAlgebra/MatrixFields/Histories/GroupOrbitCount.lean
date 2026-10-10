import Mathlib
import OAI.LinearAlgebra.MatrixFields.Histories.HistoryPositions
import OAI.LinearAlgebra.MatrixFields.Tensors.CWStageCStatistics

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section

namespace MatrixMultiplication.RecoverySupport

variable {K X Y Z : Type*} [Zero K] [Fintype X] [Fintype Y] [Fintype Z]

def support (Q : X → Y → Z → K) : Finset (X × Y × Z) := by
  classical
  exact Finset.univ.filter fun p => Q p.1 p.2.1 p.2.2 ≠ 0

theorem support_card_le (Q : X → Y → Z → K) :
    (support Q).card ≤ Fintype.card X * Fintype.card Y * Fintype.card Z := by
  classical
  have h := Finset.card_filter_le (s := (Finset.univ : Finset (X × Y × Z)))
    (p := fun p => Q p.1 p.2.1 p.2.2 ≠ 0)
  simpa only [support, Finset.card_univ, Fintype.card_prod, Nat.mul_assoc] using h

theorem support_card_le_exp (Q : X → Y → Z → K) {bX bY bZ : ℝ} (N : ℕ)
    (hX : (Fintype.card X : ℝ) ≤ Real.exp (bX * N))
    (hY : (Fintype.card Y : ℝ) ≤ Real.exp (bY * N))
    (hZ : (Fintype.card Z : ℝ) ≤ Real.exp (bZ * N)) :
    ((support Q).card : ℝ) ≤ Real.exp ((bX + bY + bZ) * N) := by
  have hcard : ((support Q).card : ℝ) ≤
      (Fintype.card X : ℝ) * Fintype.card Y * Fintype.card Z := by
    exact_mod_cast support_card_le Q
  calc
    ((support Q).card : ℝ) ≤
        (Fintype.card X : ℝ) * Fintype.card Y * Fintype.card Z := hcard
    _ ≤ (Real.exp (bX * N) * Real.exp (bY * N)) * Real.exp (bZ * N) :=
      mul_le_mul (mul_le_mul hX hY (Nat.cast_nonneg _) (Real.exp_pos _).le)
        hZ (Nat.cast_nonneg _) (mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le)
    _ = Real.exp ((bX + bY + bZ) * N) := by
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
      ring

theorem word_card_eq_exp {d : ℕ} (hd : 0 < d) (a N : ℕ) :
    (Fintype.card (Fin (a * N) → Fin d) : ℝ) =
      Real.exp (((a : ℝ) * Real.log (d : ℝ)) * N) := by
  have hdr : 0 < (d : ℝ) := by exact_mod_cast hd
  simp only [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow]
  calc
    (d : ℝ) ^ (a * N) = Real.exp (((a * N : ℕ) : ℝ) * Real.log (d : ℝ)) := by
      rw [Real.exp_nat_mul, Real.exp_log hdr]
    _ = Real.exp (((a : ℝ) * Real.log (d : ℝ)) * N) := by
      simp only [Nat.cast_mul]
      congr 1
      ring

theorem card_le_exp_of_word_embedding {d : ℕ} (hd : 0 < d) (a N : ℕ)
    (e : X ↪ (Fin (a * N) → Fin d)) :
    (Fintype.card X : ℝ) ≤ Real.exp (((a : ℝ) * Real.log (d : ℝ)) * N) := by
  rw [← word_card_eq_exp hd a N]
  exact_mod_cast Fintype.card_le_of_injective e e.injective

theorem support_card_le_exp_of_word_embeddings (Q : X → Y → Z → K)
    {d : ℕ} (hd : 0 < d) (a N : ℕ)
    (ex : X ↪ (Fin (a * N) → Fin d))
    (ey : Y ↪ (Fin (a * N) → Fin d))
    (ez : Z ↪ (Fin (a * N) → Fin d)) :
    ((support Q).card : ℝ) ≤ Real.exp ((3 * (a : ℝ) * Real.log (d : ℝ)) * N) := by
  have h := support_card_le_exp Q N
    (card_le_exp_of_word_embedding hd a N ex)
    (card_le_exp_of_word_embedding hd a N ey)
    (card_le_exp_of_word_embedding hd a N ez)
  convert h using 1
  congr 1
  ring

def cw5SupportRate (a : ℕ) : ℝ := 3 * (a : ℝ) * Real.log 7 + 1

theorem cw5SupportRate_pos (a : ℕ) : 0 < cw5SupportRate a := by
  have hlog : 0 ≤ Real.log 7 := Real.log_nonneg (by norm_num)
  have h := mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 3) (Nat.cast_nonneg a)) hlog
  unfold cw5SupportRate
  linarith

theorem cw5_support_card_le_exp (Q : X → Y → Z → K) (a N : ℕ)
    (ex : X ↪ (Fin (a * N) → Fin 7))
    (ey : Y ↪ (Fin (a * N) → Fin 7))
    (ez : Z ↪ (Fin (a * N) → Fin 7)) :
    ((support Q).card : ℝ) ≤ Real.exp (cw5SupportRate a * N) := by
  apply (support_card_le_exp_of_word_embeddings Q (by norm_num) a N ex ey ez).trans
  apply Real.exp_le_exp.mpr
  unfold cw5SupportRate
  simp only [Nat.cast_ofNat]
  exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one) (Nat.cast_nonneg N)

end MatrixMultiplication.RecoverySupport

end
end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section

open scoped BigOperators

namespace MatrixMultiplication.HistorySupport

variable {H : Type*}

abbrev HistoryWords (P : H → Type*) (l r : H → ℕ) (d : ℕ) :=
  ∀ h, P h → ((Fin (l h) → Fin d) × (Fin (r h) → Fin d))

def totalLength [Fintype H] (P : H → Type*) [∀ h, Fintype (P h)]
    (l r : H → ℕ) : ℕ :=
  ∑ h, Fintype.card (P h) * (l h + r h)

variable [Fintype H] [DecidableEq H]
variable (P : H → Type*) [∀ h, Fintype (P h)] [∀ h, DecidableEq (P h)]
variable (l r : H → ℕ)

theorem card_historyWords (d : ℕ) :
    Fintype.card (HistoryWords P l r d) = d ^ totalLength P l r := by
  change Fintype.card (∀ h, P h → ((Fin (l h) → Fin d) × (Fin (r h) → Fin d))) = _
  rw [Fintype.card_pi]
  simp only [Fintype.card_fun, Fintype.card_prod, Fintype.card_fin, ← pow_add, ← pow_mul]
  rw [Finset.prod_pow_eq_pow_sum]
  congr 1
  unfold totalLength
  apply Finset.sum_congr rfl
  intro h _
  exact Nat.mul_comm _ _

theorem card_historyWords_le_pow {d : ℕ} (hd : 0 < d) (a N : ℕ)
    (hlen : totalLength P l r ≤ a * N) :
    Fintype.card (HistoryWords P l r d) ≤ d ^ (a * N) := by
  rw [card_historyWords]
  exact Nat.pow_le_pow_right hd hlen

theorem card_historyWords_le_exp {d : ℕ} (hd : 0 < d) (a N : ℕ)
    (hlen : totalLength P l r ≤ a * N) :
    (Fintype.card (HistoryWords P l r d) : ℝ) ≤
      Real.exp (((a : ℝ) * Real.log (d : ℝ)) * N) := by
  have hpow : ((d ^ (a * N) : ℕ) : ℝ) =
      Real.exp (((a : ℝ) * Real.log (d : ℝ)) * N) := by
    simpa only [Fintype.card_fun, Fintype.card_fin] using
      RecoverySupport.word_card_eq_exp hd a N
  rw [← hpow]
  exact_mod_cast card_historyWords_le_pow P l r hd a N hlen

theorem support_card_le_exp {K : Type*} [Zero K] {d : ℕ} (hd : 0 < d)
    (Q : HistoryWords P l r d → HistoryWords P l r d → HistoryWords P l r d → K)
    (a N : ℕ) (hlen : totalLength P l r ≤ a * N) :
    ((RecoverySupport.support Q).card : ℝ) ≤
      Real.exp ((3 * (a : ℝ) * Real.log (d : ℝ)) * N) := by
  have hdim := card_historyWords_le_exp P l r hd a N hlen
  have h := RecoverySupport.support_card_le_exp Q N hdim hdim hdim
  convert h using 1
  congr 1
  ring

theorem cw5_support_card_le_exp {K : Type*} [Zero K]
    (Q : HistoryWords P l r 7 → HistoryWords P l r 7 → HistoryWords P l r 7 → K)
    (a N : ℕ) (hlen : totalLength P l r ≤ a * N) :
    ((RecoverySupport.support Q).card : ℝ) ≤
      Real.exp (RecoverySupport.cw5SupportRate a * N) := by
  apply (support_card_le_exp P l r (by norm_num) Q a N hlen).trans
  apply Real.exp_le_exp.mpr
  unfold RecoverySupport.cw5SupportRate
  simp only [Nat.cast_ofNat]
  exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one) (Nat.cast_nonneg N)

end MatrixMultiplication.HistorySupport

end
end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.AllFieldHistory

open AllFieldParameters
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq

theorem work_source_amount_pos {K : ℕ} (allocation : Allocation) (w : PlacedWork K) :
    0 < amount allocation (w.1.source, w.2) := by
  apply div_pos _ (by norm_num)
  cases w.1 with
  | stageA h => exact initialAmount_pos h.val
  | stageB h => exact aAmount_pos h.val
  | stageC h => exact partAmount_pos allocation h

theorem work_source_population_pos {K : ℕ} (allocation : Allocation) {dilation : ℕ}
    (hd : 0 < dilation) (w : PlacedWork K) :
    0 < population allocation dilation (w.1.source, w.2) :=
  (AllFieldPopulationCounts.count_pos_iff _ (amount_nonneg allocation) hd _).mpr
    (work_source_amount_pos allocation w)

abbrev PositiveBranch {K : ℕ} (allocation : Allocation) (w : PlacedWork K) :=
  {b : w.1.Branch // 0 < amount allocation (w.1.child b false, w.2)}

theorem branchPopulation_pos_iff {K : ℕ} (allocation : Allocation) {dilation : ℕ}
    (hd : 0 < dilation) (w : PlacedWork K) (b : w.1.Branch) :
    0 < branchPopulation allocation dilation w b ↔
      0 < amount allocation (w.1.child b false, w.2) :=
  AllFieldPopulationCounts.count_pos_iff _ (amount_nonneg allocation) hd _

theorem positive_branch_minimum {K : ℕ} (allocation : Allocation) (dilation : ℕ)
    (w : PlacedWork K) (b : PositiveBranch allocation w) :
    dilation ≤ branchPopulation allocation dilation w b.val :=
  AllFieldPopulationCounts.dilation_le_count _ (amount_nonneg allocation) dilation _ b.property

theorem positive_joint_class_minimum {K : ℕ} (allocation : Allocation) {dilation : ℕ}
    (hd : 0 < dilation) (w : PlacedWork K) (u : JointPopulation.Shape)
    (hu : 0 < jointCounts allocation dilation w u) : dilation ≤ jointCounts allocation dilation w u := by
  obtain ⟨b, rfl, hb⟩ := shapeCounts_positive _ _ u hu
  rw [jointCounts_at]
  exact positive_branch_minimum allocation dilation w
    ⟨b, (branchPopulation_pos_iff allocation hd w b).mp hb⟩

def activeLengthRate {K tick : ℕ} (allocation : Allocation) : ℚ :=
  ∑ h : Active K tick, amount allocation (h.val.1.source, h.val.2) *
    (2 * h.val.1.halfLength : ℕ)

def activePositions {K tick : ℕ} (allocation : Allocation) (dilation : ℕ)
    (h : Active K tick) : Type :=
  Fin (population allocation dilation (h.val.1.source, h.val.2))

instance {K tick : ℕ} (allocation : Allocation) (dilation : ℕ) (h : Active K tick) :
    Fintype (activePositions allocation dilation h) := inferInstanceAs (Fintype (Fin _))

theorem active_totalLength_cast {K tick : ℕ} (allocation : Allocation) (dilation : ℕ) :
    (HistorySupport.totalLength (activePositions (K := K) (tick := tick) allocation dilation)
      activeHalfLength activeHalfLength : ℚ) =
      (populationLength (K := K) allocation dilation : ℚ) *
        activeLengthRate (K := K) (tick := tick) allocation := by
  simp only [HistorySupport.totalLength, Nat.cast_sum, Nat.cast_mul,
    activeLengthRate, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro h hh
  simp only [Fintype.card_eq_nat_card]
  simp only [activePositions, Nat.card_fin, population_cast, activeHalfLength]
  push_cast
  ring

def activeLengthBudget {K tick : ℕ} (allocation : Allocation) : ℕ :=
  Nat.ceil (activeLengthRate (K := K) (tick := tick) allocation)

theorem active_totalLength_le {K tick : ℕ} (allocation : Allocation) (dilation : ℕ) :
    HistorySupport.totalLength (activePositions (K := K) (tick := tick) allocation dilation)
      activeHalfLength activeHalfLength ≤
      activeLengthBudget (K := K) (tick := tick) allocation *
        populationLength (K := K) allocation dilation := by
  have h := active_totalLength_cast (K := K) (tick := tick) allocation dilation
  have hc : activeLengthRate (K := K) (tick := tick) allocation ≤
      (activeLengthBudget (K := K) (tick := tick) allocation : ℚ) := Nat.le_ceil _
  have hb := mul_le_mul_of_nonneg_left hc
    (Nat.cast_nonneg (populationLength (K := K) allocation dilation) :
      (0 : ℚ) ≤ populationLength (K := K) allocation dilation)
  rw [← h] at hb
  exact_mod_cast hb.trans_eq (mul_comm _ _)

theorem active_cw5_support_bound {F : Type*} [Zero F] {K tick : ℕ}
    (allocation : Allocation) (dilation : ℕ)
    (Q : HistorySupport.HistoryWords
      (activePositions (K := K) (tick := tick) allocation dilation)
      activeHalfLength activeHalfLength 7 →
      HistorySupport.HistoryWords
        (activePositions (K := K) (tick := tick) allocation dilation)
        activeHalfLength activeHalfLength 7 →
      HistorySupport.HistoryWords
        (activePositions (K := K) (tick := tick) allocation dilation)
        activeHalfLength activeHalfLength 7 → F) :
    ((RecoverySupport.support Q).card : ℝ) ≤
      Real.exp (RecoverySupport.cw5SupportRate
        (activeLengthBudget (K := K) (tick := tick) allocation) *
          (populationLength (K := K) allocation dilation : ℝ)) :=
  HistorySupport.cw5_support_card_le_exp _ _ _ Q _ _
    (active_totalLength_le allocation dilation)

end MatrixMultiplication.AllFieldHistory

end
end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section

namespace MatrixMultiplication.AllFieldHistorySupport

open AllFieldHistory
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq

theorem population_dilation {K : ℕ} (allocation : Allocation) (m : ℕ) (h : History K) :
    population allocation m h = m * population allocation 1 h := by
  simp only [population, AllFieldPopulationCounts.count, one_mul]

theorem branchPopulation_dilation {K : ℕ} (allocation : Allocation) (m : ℕ)
    (w : PlacedWork K) (b : w.1.Branch) :
    branchPopulation allocation m w b = m * branchPopulation allocation 1 w b := by
  simp only [branchPopulation, population, AllFieldPopulationCounts.count, one_mul]

theorem jointCounts_dilation {K : ℕ} (allocation : Allocation) (m : ℕ)
    (w : PlacedWork K) (u : JointPopulation.Shape) :
    jointCounts allocation m w u = m * jointCounts allocation 1 w u := by
  simp only [jointCounts, shapeCounts, branchPopulation, population,
    AllFieldPopulationCounts.count, one_mul, Finset.mul_sum, mul_ite, mul_zero]

theorem activeCounts_dilation {K tick : ℕ} (allocation : Allocation) (m : ℕ)
    (h : Active K tick) (u : JointPopulation.Shape) :
    activeCounts allocation m h u = m * activeCounts allocation 1 h u :=
  jointCounts_dilation allocation m h.val u

theorem activeCounts_pos_iff {K tick m : ℕ} (allocation : Allocation) (hm : 0 < m)
    (h : Active K tick) (u : JointPopulation.Shape) :
    0 < activeCounts allocation m h u ↔ 0 < activeCounts allocation 1 h u := by
  rw [activeCounts_dilation]
  exact Nat.mul_pos_iff_of_pos_left hm

theorem dilation_le_activeCounts {K tick : ℕ} (allocation : Allocation) (m : ℕ)
    (h : Active K tick) (u : JointPopulation.Shape)
    (hpos : 0 < activeCounts allocation 1 h u) : m ≤ activeCounts allocation m h u := by
  rw [activeCounts_dilation]
  calc
    m = m * 1 := (Nat.mul_one m).symm
    _ ≤ m * activeCounts allocation 1 h u := Nat.mul_le_mul_left m hpos

theorem two_le_activeCounts {K tick m : ℕ} (allocation : Allocation) (hm : 2 ≤ m)
    (h : Active K tick) (u : JointPopulation.Shape)
    (hpos : 0 < activeCounts allocation 1 h u) : 2 ≤ activeCounts allocation m h u :=
  hm.trans (dilation_le_activeCounts allocation m h u hpos)

theorem totalLength_dilation {K tick : ℕ} (allocation : Allocation) (m : ℕ)
    (l r : Active K tick → ℕ) :
    HistorySupport.totalLength (JointPopulation.Positions (activeCounts allocation m)) l r =
      m * HistorySupport.totalLength (JointPopulation.Positions (activeCounts allocation 1)) l r := by
  simp only [HistorySupport.totalLength, JointPopulation.Positions, Fintype.card_fin,
    activeCounts_dilation allocation m, ← Finset.mul_sum, Nat.mul_assoc]

def fixedBaseLength {K tick : ℕ} (allocation : Allocation) : ℕ :=
  HistorySupport.totalLength
    (JointPopulation.Positions (activeCounts (K := K) (tick := tick) allocation 1))
    activeHalfLength activeHalfLength

def supportRate {K tick : ℕ} (allocation : Allocation) : ℝ :=
  RecoverySupport.cw5SupportRate (fixedBaseLength (K := K) (tick := tick) allocation)

theorem supportRate_pos {K tick : ℕ} (allocation : Allocation) :
    0 < supportRate (K := K) (tick := tick) allocation :=
  RecoverySupport.cw5SupportRate_pos _

abbrev ActiveRawPairs {K tick : ℕ} (allocation : Allocation) (m : ℕ) :=
  JointCanonicalization.RawPairs (activeCounts (K := K) (tick := tick) allocation m)
    (JointCanonicalCW.Left activeHalfLength) (JointCanonicalCW.Right activeHalfLength)

theorem raw_support_card_le_exp {K tick : ℕ} {F : Type*} [Zero F]
    (allocation : Allocation) (m : ℕ)
    (Q : ActiveRawPairs (K := K) (tick := tick) allocation m →
      ActiveRawPairs (K := K) (tick := tick) allocation m →
      ActiveRawPairs (K := K) (tick := tick) allocation m → F) :
    ((RecoverySupport.support Q).card : ℝ) ≤
      Real.exp (supportRate (K := K) (tick := tick) allocation * m) := by
  apply HistorySupport.cw5_support_card_le_exp
    (JointPopulation.Positions (activeCounts (K := K) (tick := tick) allocation m))
    activeHalfLength activeHalfLength Q (fixedBaseLength (K := K) (tick := tick) allocation) m
  rw [totalLength_dilation]
  exact le_of_eq (Nat.mul_comm _ _)

abbrev ActiveClass (K tick : ℕ) := Active K tick × JointPopulation.Shape

def selectedBaseCount {K tick : ℕ} (allocation : Allocation)
    (D : Finset (ActiveClass K tick)) : ℕ :=
  ∑ c ∈ D, activeCounts allocation 1 c.1 c.2

def selectedBasePopulation {K tick : ℕ} (allocation : Allocation)
    (D : Finset (ActiveClass K tick)) : ℝ := (selectedBaseCount allocation D : ℝ)

abbrev selectedPositions {K tick : ℕ} (allocation : Allocation) (m : ℕ)
    (D : Finset (ActiveClass K tick)) (c : D) :=
  JointCanonicalization.ClassPositions (activeCounts allocation m) c.val

theorem selected_count_dilation {K tick : ℕ} (allocation : Allocation) (m : ℕ)
    (D : Finset (ActiveClass K tick)) :
    (∑ c ∈ D, activeCounts allocation m c.1 c.2) = m * selectedBaseCount allocation D := by
  simp only [selectedBaseCount, activeCounts_dilation allocation m, Finset.mul_sum]

theorem selectedBaseCount_pos {K tick : ℕ} (allocation : Allocation)
    (D : Finset (ActiveClass K tick)) (hD : D.Nonempty)
    (hpos : ∀ c ∈ D, 0 < activeCounts allocation 1 c.1 c.2) :
    0 < selectedBaseCount allocation D :=
  Finset.sum_pos hpos hD

theorem selectedBasePopulation_pos {K tick : ℕ} (allocation : Allocation)
    (D : Finset (ActiveClass K tick)) (hD : D.Nonempty)
    (hpos : ∀ c ∈ D, 0 < activeCounts allocation 1 c.1 c.2) :
    0 < selectedBasePopulation allocation D := by
  unfold selectedBasePopulation
  exact_mod_cast selectedBaseCount_pos allocation D hD hpos

theorem selected_populationSize {K tick : ℕ} (allocation : Allocation) (m : ℕ)
    (D : Finset (ActiveClass K tick)) :
    PermutationMatching.populationSize (selectedPositions allocation m D) =
      selectedBasePopulation allocation D * (m : ℝ) := by
  simp only [PermutationMatching.populationSize, selectedPositions,
    JointCanonicalization.ClassPositions, Fintype.card_fin]
  rw [Finset.sum_coe_sort D
    (fun c : ActiveClass K tick => (activeCounts allocation m c.1 c.2 : ℝ))]
  simp only [activeCounts_dilation allocation m, Nat.cast_mul, ← Finset.mul_sum,
    selectedBasePopulation, selectedBaseCount, Nat.cast_sum]
  exact mul_comm _ _

theorem selected_two_le {K tick m : ℕ} (allocation : Allocation) (hm : 2 ≤ m)
    (D : Finset (ActiveClass K tick))
    (hpos : ∀ c ∈ D, 0 < activeCounts allocation 1 c.1 c.2) (c : D) :
    2 ≤ Fintype.card (selectedPositions allocation m D c) := by
  simpa only [selectedPositions, JointCanonicalization.ClassPositions, Fintype.card_fin] using
    two_le_activeCounts allocation hm c.val.1 c.val.2 (hpos c.val c.property)

theorem selected_classWeight_formula {K tick m : ℕ} (allocation : Allocation)
    (hm : 0 < m) (D : Finset (ActiveClass K tick)) (c : D) :
    PermutationMatching.classWeight (selectedPositions allocation m D) c =
      (activeCounts allocation 1 c.val.1 c.val.2 : ℝ) / selectedBasePopulation allocation D := by
  rw [PermutationMatching.classWeight, selected_populationSize]
  simp only [selectedPositions, JointCanonicalization.ClassPositions, Fintype.card_fin,
    activeCounts_dilation allocation m, Nat.cast_mul]
  rw [mul_comm (selectedBasePopulation allocation D) (m : ℝ)]
  exact mul_div_mul_left _ _ (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hm))

theorem selected_classWeight_eq_one {K tick m : ℕ} (allocation : Allocation)
    (hm : 0 < m) (D : Finset (ActiveClass K tick)) (c : D) :
    PermutationMatching.classWeight (selectedPositions allocation m D) c =
      PermutationMatching.classWeight (selectedPositions allocation 1 D) c :=
  (selected_classWeight_formula allocation hm D c).trans
    (selected_classWeight_formula allocation (by decide : 0 < (1 : ℕ)) D c).symm

theorem selected_classProductMixture_eq_one {K tick m : ℕ} (allocation : Allocation)
    (hm : 0 < m) (D : Finset (ActiveClass K tick)) (left right : D → ℝ) :
    PermutationMatching.classProductMixture (selectedPositions allocation m D) left right =
      PermutationMatching.classProductMixture (selectedPositions allocation 1 D) left right := by
  unfold PermutationMatching.classProductMixture
  apply Finset.sum_congr rfl
  intro c _
  rw [selected_classWeight_eq_one allocation hm D c]

theorem work_source_amount_pos {K : ℕ} (allocation : Allocation) (w : PlacedWork K) :
    0 < amount allocation (w.1.source, w.2) := by
  rcases w with ⟨w, phi⟩
  unfold amount
  apply div_pos _ (by norm_num)
  cases w with
  | stageA h => exact initialAmount_pos h.val
  | stageB h => exact aAmount_pos h.val
  | stageC h => exact partAmount_pos allocation h

theorem work_source_population_pos {K m : ℕ} (allocation : Allocation) (hm : 0 < m)
    (w : PlacedWork K) : 0 < population allocation m (w.1.source, w.2) :=
  (AllFieldPopulationCounts.count_pos_iff (amount allocation) (amount_nonneg allocation)
    hm (w.1.source, w.2)).2 (work_source_amount_pos allocation w)

def positiveClasses {K tick : ℕ} (allocation : Allocation) (h : Active K tick) :
    Finset (ActiveClass K tick) :=
  Finset.univ.filter fun c => c.1 = h ∧ 0 < activeCounts allocation 1 c.1 c.2

theorem positiveClasses_positive {K tick : ℕ} (allocation : Allocation) (h : Active K tick)
    (c : ActiveClass K tick) (hc : c ∈ positiveClasses allocation h) :
    0 < activeCounts allocation 1 c.1 c.2 := (Finset.mem_filter.mp hc).2.2

theorem positiveClasses_baseCount {K tick : ℕ} (allocation : Allocation) (h : Active K tick) :
    selectedBaseCount allocation (positiveClasses allocation h) =
      population allocation 1 (h.val.1.source, h.val.2) := by
  have hkeep (n : ℕ) : (if 0 < n then n else 0) = n := by
    split_ifs <;> omega
  calc
    selectedBaseCount allocation (positiveClasses allocation h) =
        ∑ u, activeCounts allocation 1 h u := by
      simp [selectedBaseCount, positiveClasses, Finset.sum_filter, ite_and, hkeep,
        Fintype.sum_prod_type]
    _ = population allocation 1 (h.val.1.source, h.val.2) :=
      jointCounts_sum allocation 1 h.val

theorem positiveClasses_basePopulation_pos {K tick : ℕ} (allocation : Allocation)
    (h : Active K tick) : 0 < selectedBasePopulation allocation (positiveClasses allocation h) := by
  unfold selectedBasePopulation
  rw [positiveClasses_baseCount]
  exact_mod_cast work_source_population_pos allocation (by decide : 0 < (1 : ℕ)) h.val

theorem positiveClasses_nonempty {K tick : ℕ} (allocation : Allocation) (h : Active K tick) :
    (positiveClasses allocation h).Nonempty := by
  by_contra hn
  have hempty := Finset.not_nonempty_iff_eq_empty.mp hn
  have hp := positiveClasses_basePopulation_pos allocation h
  simp [selectedBasePopulation, selectedBaseCount, hempty] at hp

theorem positiveClasses_populationSize {K tick : ℕ} (allocation : Allocation) (m : ℕ)
    (h : Active K tick) :
    PermutationMatching.populationSize
      (selectedPositions allocation m (positiveClasses allocation h)) =
        (population allocation 1 (h.val.1.source, h.val.2) : ℝ) * m := by
  rw [selected_populationSize]
  simp only [selectedBasePopulation, positiveClasses_baseCount]

end MatrixMultiplication.AllFieldHistorySupport

end
end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section

namespace MatrixMultiplication.AllFieldHistoryIncomingMasks

open MatrixMultiplication.Foundation AllFieldHistory AllFieldParameters
open AllFieldHistoryChildLaws AllFieldHistorySupport
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq

variable {K tick : ℕ}

def joinHalves (w : Work K) :
    ((Fin w.halfLength → Fin 7) × (Fin w.halfLength → Fin 7)) →
      (Fin (currentLength w.source) → Fin 7) :=
  match w with
  | .stageA _ => fun x => Fin.append x.1 x.2
  | .stageB _ => fun x => Fin.append x.1 x.2
  | .stageC _ => fun x => Fin.append x.1 x.2

def sourcePositionsEquiv (allocation : Allocation) (m : ℕ) (h : Active K tick) :
    JointPopulation.Positions (activeCounts allocation m) h ≃
      Fin (population allocation m (h.val.1.source, h.val.2)) :=
  finCongr (jointCounts_sum allocation m h.val)

def incomingWord (allocation : Allocation) (m : ℕ) (h : Active K tick)
    (w : ActiveRawPairs (K := K) (tick := tick) allocation m) :
    HistoryWord allocation m (h.val.1.source, h.val.2) :=
  fun p => joinHalves h.val.1 (w h ((sourcePositionsEquiv allocation m h).symm p))

def received (allocation : Allocation) (m : ℕ) (ε : ℝ) (side : Fin 3)
    (w : ActiveRawPairs (K := K) (tick := tick) allocation m) : Prop :=
  ∀ h : Active K tick,
    residentMask allocation m ε (h.val.1.source, h.val.2) side
      (incomingWord allocation m h w)

end MatrixMultiplication.AllFieldHistoryIncomingMasks

end
end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section

namespace MatrixMultiplication.AllFieldHistoryBranchWeights

open AllFieldHistory AllFieldHistorySupport AllFieldParameters
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq

theorem stageB_branchPopulation_rat {K : ℕ} (allocation : Allocation) (dilation : ℕ)
    (h : APositive K) (b : BSplit h) (phi : Placement) :
    (branchPopulation allocation dilation (.stageB h, phi) b : ℚ) =
      (population allocation dilation (.afterA h.val, phi) : ℚ) *
        stageBLaw (aShape h.val) (bSplit ⟨h, b, false⟩) := by
  simp only [branchPopulation, Work.child, population_cast, amount, canonicalAmount, bAmount]
  ring

theorem stageB_branchPopulation_real {K : ℕ} (allocation : Allocation) (dilation : ℕ)
    (h : APositive K) (b : BSplit h) (phi : Placement) :
    (branchPopulation allocation dilation (.stageB h, phi) b : ℝ) =
      (population allocation dilation (.afterA h.val, phi) : ℝ) *
        (stageBLaw (aShape h.val) (bSplit ⟨h, b, false⟩) : ℝ) := by
  exact_mod_cast stageB_branchPopulation_rat allocation dilation h b phi

theorem stageB_branchWeight_rat {K dilation : ℕ} (allocation : Allocation)
    (hd : 0 < dilation) (h : APositive K) (b : BSplit h) (phi : Placement) :
    (branchPopulation allocation dilation (.stageB h, phi) b : ℚ) /
      (population allocation dilation (.afterA h.val, phi) : ℚ) =
        stageBLaw (aShape h.val) (bSplit ⟨h, b, false⟩) := by
  have hpos := AllFieldHistorySupport.work_source_population_pos allocation hd (.stageB h, phi)
  have hden : (population allocation dilation (.afterA h.val, phi) : ℚ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt hpos
  apply (div_eq_iff hden).2
  rw [stageB_branchPopulation_rat]
  exact mul_comm _ _

theorem stageB_branchWeight_real {K dilation : ℕ} (allocation : Allocation)
    (hd : 0 < dilation) (h : APositive K) (b : BSplit h) (phi : Placement) :
    (branchPopulation allocation dilation (.stageB h, phi) b : ℝ) /
      (population allocation dilation (.afterA h.val, phi) : ℝ) =
        (stageBLaw (aShape h.val) (bSplit ⟨h, b, false⟩) : ℝ) := by
  have hpos := AllFieldHistorySupport.work_source_population_pos allocation hd (.stageB h, phi)
  have hden : (population allocation dilation (.afterA h.val, phi) : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt hpos
  apply (div_eq_iff hden).2
  rw [stageB_branchPopulation_real]
  exact mul_comm _ _

theorem shapeCounts_weighted_sum {I : Type*} [Fintype I]
    (code : I → JointPopulation.Shape) (weight : I → ℕ)
    (f : JointPopulation.Shape → ℝ) :
    (∑ u, (shapeCounts code weight u : ℝ) * f u) =
      ∑ b, (weight b : ℝ) * f (code b) := by
  simp only [shapeCounts, Nat.cast_sum, Nat.cast_ite, Nat.cast_zero, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  simp [ite_mul]

end MatrixMultiplication.AllFieldHistoryBranchWeights

end
end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section

namespace MatrixMultiplication.AllFieldHistoryStageCIncoming

open AllFieldHistory AllFieldHistorySupport AllFieldParameters
open CWStageCProducts InheritedMasks
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq

variable {K tick : ℕ}

def stageCActive (h : PartC K) (phi : Placement)
    (ht : FiniteSchedule.lotTick (Work.stageC h).lot (Work.stageC h).stage = tick) :
    Active K tick := ⟨(.stageC h, phi), ht⟩

def positionEquiv (allocation : Allocation) (dilation : ℕ) (h : PartC K)
    (phi : Placement)
    (ht : FiniteSchedule.lotTick (Work.stageC h).lot (Work.stageC h).stage = tick)
    (e : JointPopulation.Target (activeCounts (K := K) (tick := tick) allocation dilation)) :
    JointPopulation.Positions (activeCounts (K := K) (tick := tick) allocation dilation) (stageCActive h phi ht) ≃
      CWStageCProducts.Positions (populationAtomCounts allocation dilation (h, phi)) :=
  (JointCanonicalization.positionEquiv (activeCounts (K := K) (tick := tick) allocation dilation) e
    (stageCActive h phi ht)).trans
      (branchPositionEquiv allocation dilation (.stageC h, phi))

theorem positionEquiv_shape (allocation : Allocation) (dilation : ℕ) (h : PartC K)
    (phi : Placement)
    (ht : FiniteSchedule.lotTick (Work.stageC h).lot (Work.stageC h).stage = tick)
    (e : JointPopulation.Target (activeCounts (K := K) (tick := tick) allocation dilation))
    (j : JointPopulation.Positions (activeCounts (K := K) (tick := tick) allocation dilation) (stageCActive h phi ht)) :
    branchShape (.stageC h, phi) (positionEquiv allocation dilation h phi ht e j).1 =
      (e (stageCActive h phi ht)).val j := by
  exact (branchPositionEquiv_shape allocation dilation (.stageC h, phi)
    (JointCanonicalization.positionEquiv (activeCounts (K := K) (tick := tick) allocation dilation) e
      (stageCActive h phi ht) j)).trans
    (JointCanonicalization.positionEquiv_shape (activeCounts (K := K) (tick := tick) allocation dilation) e
      (stageCActive h phi ht) j)

theorem positionEquiv_symm_shape (allocation : Allocation) (dilation : ℕ) (h : PartC K)
    (phi : Placement)
    (ht : FiniteSchedule.lotTick (Work.stageC h).lot (Work.stageC h).stage = tick)
    (e : JointPopulation.Target (activeCounts (K := K) (tick := tick) allocation dilation))
    (p : CWStageCProducts.Positions (populationAtomCounts allocation dilation (h, phi))) :
    (e (stageCActive h phi ht)).val ((positionEquiv allocation dilation h phi ht e).symm p) =
      branchShape (.stageC h, phi) p.1 := by
  have hp := positionEquiv_shape allocation dilation h phi ht e
    ((positionEquiv allocation dilation h phi ht e).symm p)
  simpa only [Equiv.apply_symm_apply] using hp.symm

theorem typeWindow_of_target_side_weights (allocation : Allocation) {dilation : ℕ}
    (hd : 0 < dilation) (h : PartC K) (phi : Placement)
    (ht : FiniteSchedule.lotTick (Work.stageC h).lot (Work.stageC h).stage = tick)
    (e : JointPopulation.Target (activeCounts (K := K) (tick := tick) allocation dilation))
    (w : ActiveRawPairs (K := K) (tick := tick) allocation dilation) (side : Fin 3)
    (hweights : ∀ j : JointPopulation.Positions (activeCounts (K := K) (tick := tick) allocation dilation)
        (stageCActive h phi ht),
      CWLeafStatistics.weight ((w (stageCActive h phi ht) j).1 (0 : Fin 1)) =
          (JointPopulation.shapeSide side ((e (stageCActive h phi ht)).val j)).val ∧
      CWLeafStatistics.weight ((w (stageCActive h phi ht) j).2 (0 : Fin 1)) =
          activeParentShape (stageCActive h phi ht) side -
            (JointPopulation.shapeSide side ((e (stageCActive h phi ht)).val j)).val)
    (η : ℝ) (hη : 0 ≤ η) :
    typeWindow
      (fun a : Fin 6 =>
        (littleLaw (cParameterParent h) (cShapeParent h) (phi.symm side) a : ℝ)) η
      (fun j => CWCompleteStatistics.twoStatistic
        (Matrix.vecCons ((w (stageCActive h phi ht) j).1 (0 : Fin 1)) (Matrix.vecCons ((w (stageCActive h phi ht) j).2 (0 : Fin 1)) Matrix.vecEmpty))) := by
  let p := positionEquiv allocation dilation h phi ht e
  let words : CWStageCProducts.Positions (populationAtomCounts allocation dilation (h, phi)) →
      CWStageCProducts.Word := fun j =>
    (Matrix.vecCons ((w (stageCActive h phi ht) (p.symm j)).1 (0 : Fin 1)) (Matrix.vecCons ((w (stageCActive h phi ht) (p.symm j)).2 (0 : Fin 1)) Matrix.vecEmpty))
  have hgeometry (j : CWStageCProducts.Positions
      (populationAtomCounts allocation dilation (h, phi))) :
      CWLeafStatistics.weight (words j 0) =
        branchAtom (stageCDistinguished (cShapeParent h)) j.1 (phi.symm side) ∧
      CWLeafStatistics.weight (words j 1) =
        CWStageCProducts.shape (stageCDistinguished (cShapeParent h)) (phi.symm side) -
          branchAtom (stageCDistinguished (cShapeParent h)) j.1 (phi.symm side) := by
    have hw := hweights (p.symm j)
    have hs := positionEquiv_symm_shape allocation dilation h phi ht e j
    change (e (stageCActive h phi ht)).val (p.symm j) = _ at hs
    rw [hs] at hw
    simpa only [words, Matrix.cons_val_zero, Matrix.cons_val_one,
      activeParentShape, stageCActive, Work.parentShape, branchShape,
      encodePhysicalShape_side, physicalShape, Work.splitShape, cSplit,
      branchAtom_eq_stageCAtom, shape_eq_parent (cShapeParent h) (bShape_size h.1.val)
        h.1.property] using hw
  have hwindow := typeWindow_of_placed_side_weights
    (populationAtomCounts allocation dilation (h, phi))
    (cParameterParent h) (cShapeParent h) (bShape_size h.1.val) h.1.property
    (population allocation dilation (.partC h, phi))
    (AllFieldHistorySupport.work_source_population_pos allocation hd (.stageC h, phi))
    (populationAtomCounts_parent allocation dilation (h, phi))
    phi side words hgeometry η hη
  exact (JointCanonicalization.typeWindow_reindex _ η
    (fun j => CWCompleteStatistics.twoStatistic
      (Matrix.vecCons ((w (stageCActive h phi ht) j).1 (0 : Fin 1)) (Matrix.vecCons ((w (stageCActive h phi ht) j).2 (0 : Fin 1)) Matrix.vecEmpty)))
    p.symm).mp hwindow

end MatrixMultiplication.AllFieldHistoryStageCIncoming

end
end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
namespace MatrixMultiplication.PermutationMatching

open scoped BigOperators
open Classical

noncomputable section

variable {C : Type*} [Fintype C] [DecidableEq C]
  {P X Y : C → Type*}
  [∀ c, Fintype (P c)] [∀ c, DecidableEq (P c)]
  [∀ c, Fintype (X c)] [∀ c, DecidableEq (X c)]
  [∀ c, Fintype (Y c)] [∀ c, DecidableEq (Y c)]

abbrev PairProfile (P X Y : C → Type*) [∀ c, Fintype (P c)] :=
  InheritedMasks.Profile P X × InheritedMasks.Profile P Y

def pairProfile (w : CompleteWordPair P X Y) : PairProfile P X Y :=
  (InheritedMasks.profile P X w.left, InheritedMasks.profile P Y w.right)

omit [Fintype C] [DecidableEq C] [∀ c, DecidableEq (P c)]
  [∀ c, Fintype (X c)] [∀ c, Fintype (Y c)] in
theorem pairProfile_smul (g : HalfClassPermutations P)
    (w : CompleteWordPair P X Y) : pairProfile (g • w) = pairProfile w := by
  apply Prod.ext
  · apply (InheritedMasks.profile_eq_iff P X _ _).mpr
    exact ⟨fun c => g.1 c, fun c => by
      funext i
      simp⟩
  · apply (InheritedMasks.profile_eq_iff P Y _ _).mpr
    exact ⟨fun c => g.2 c, fun c => by
      funext i
      simp⟩

omit [Fintype C] [DecidableEq C]
  [∀ c, Fintype (P c)] [∀ c, DecidableEq (P c)]
  [∀ c, Fintype (X c)] [∀ c, DecidableEq (X c)]
  [∀ c, Fintype (Y c)] [∀ c, DecidableEq (Y c)] in
private theorem completeWordPair_ext {w v : CompleteWordPair P X Y}
    (hl : w.left = v.left) (hr : w.right = v.right) : w = v := by
  cases w
  cases v
  cases hl
  cases hr
  rfl

omit [Fintype C] [DecidableEq C] [∀ c, DecidableEq (P c)]
  [∀ c, Fintype (X c)] [∀ c, Fintype (Y c)] in
theorem pairProfile_eq_iff (w v : CompleteWordPair P X Y) :
    pairProfile w = pairProfile v ↔
      ∃ g : HalfClassPermutations P, g • w = v := by
  constructor
  · intro h
    have hl := (InheritedMasks.profile_eq_iff P X w.left v.left).mp
      (congrArg Prod.fst h)
    have hr := (InheritedMasks.profile_eq_iff P Y w.right v.right).mp
      (congrArg Prod.snd h)
    obtain ⟨el, hel⟩ := hl
    obtain ⟨er, her⟩ := hr
    refine ⟨(fun c => (el c)⁻¹, fun c => (er c)⁻¹), ?_⟩
    apply completeWordPair_ext
    · funext c i
      exact congrFun (hel c) i
    · funext c i
      exact congrFun (her c) i
  · rintro ⟨g, rfl⟩
    exact (pairProfile_smul g w).symm

omit [Fintype C] [DecidableEq C] [∀ c, DecidableEq (P c)]
  [∀ c, Fintype (X c)] [∀ c, Fintype (Y c)] in
theorem pairProfile_eq_iff_orbitRel (w v : CompleteWordPair P X Y) :
    pairProfile w = pairProfile v ↔
      MulAction.orbitRel (HalfClassPermutations P) (CompleteWordPair P X Y) w v := by
  constructor
  · intro h
    obtain ⟨g, hg⟩ := (pairProfile_eq_iff v w).mp h.symm
    exact ⟨g, hg⟩
  · rintro ⟨g, rfl⟩
    exact pairProfile_smul g v

abbrev PairOrbit (P X Y : C → Type*) :=
  MulAction.orbitRel.Quotient (HalfClassPermutations P) (CompleteWordPair P X Y)

def pairOrbitProfile : PairOrbit P X Y → PairProfile P X Y :=
  Quotient.lift pairProfile fun w v h => (pairProfile_eq_iff_orbitRel w v).mpr h

omit [Fintype C] [DecidableEq C] [∀ c, DecidableEq (P c)]
  [∀ c, Fintype (X c)] [∀ c, Fintype (Y c)] in
theorem pairOrbitProfile_injective :
    Function.Injective (pairOrbitProfile (P := P) (X := X) (Y := Y)) := by
  intro q r
  induction q using Quotient.inductionOn with
  | h w =>
    induction r using Quotient.inductionOn with
    | h v =>
      intro h
      apply Quotient.sound
      exact (pairProfile_eq_iff_orbitRel w v).mp h

omit [∀ c, DecidableEq (P c)] in
theorem card_pairOrbits_le :
    Nat.card (PairOrbit P X Y) ≤
      (∏ c, (Fintype.card (P c) + 1) ^ Fintype.card (X c)) *
      (∏ c, (Fintype.card (P c) + 1) ^ Fintype.card (Y c)) := by
  have : Finite (PairOrbit P X Y) :=
    Finite.of_injective pairOrbitProfile pairOrbitProfile_injective
  let := Fintype.ofFinite (PairOrbit P X Y)
  rw [Nat.card_eq_fintype_card]
  calc
    _ ≤ Fintype.card (PairProfile P X Y) :=
      Fintype.card_le_of_injective pairOrbitProfile pairOrbitProfile_injective
    _ = _ := by
      rw [Fintype.card_prod, InheritedMasks.card_profile, InheritedMasks.card_profile]

omit [∀ c, DecidableEq (P c)] in
theorem card_pairOrbits_le_common_bound (m : ℕ)
    (hm : ∀ c, Fintype.card (P c) ≤ m) :
    Nat.card (PairOrbit P X Y) ≤ (m + 1) ^
      ((∑ c, Fintype.card (X c)) + ∑ c, Fintype.card (Y c)) := by
  refine (card_pairOrbits_le (P := P) (X := X) (Y := Y)).trans ?_
  calc
    _ ≤ (∏ c, (m + 1) ^ Fintype.card (X c)) *
        (∏ c, (m + 1) ^ Fintype.card (Y c)) := by
      apply Nat.mul_le_mul
      · exact Finset.prod_le_prod fun c _ =>
          Nat.pow_le_pow_left (Nat.add_le_add_right (hm c) 1) _
      · exact Finset.prod_le_prod fun c _ =>
          Nat.pow_le_pow_left (Nat.add_le_add_right (hm c) 1) _
    _ = _ := by rw [Finset.prod_pow_eq_pow_sum, Finset.prod_pow_eq_pow_sum, pow_add]

end

end MatrixMultiplication.PermutationMatching

end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section

namespace MatrixMultiplication.AllFieldHistoryOrbitCount

open AllFieldHistory AllFieldHistorySupport PermutationMatching
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq

abbrev Classes (K tick : ℕ) := ActiveClass K tick

abbrev Positions {K tick : ℕ} (allocation : Allocation) (m : ℕ)
    (c : Classes K tick) :=
  JointCanonicalization.ClassPositions (activeCounts allocation m) c

abbrev Letters {K tick : ℕ} (c : Classes K tick) :=
  Fin (activeHalfLength c.1) → Fin 7

abbrev ActualOrbit {K tick : ℕ} (allocation : Allocation) (m : ℕ) :=
  PairOrbit (Positions (K := K) (tick := tick) allocation m)
    (Letters (K := K) (tick := tick)) (Letters (K := K) (tick := tick))

noncomputable instance actualOrbitFintype {K tick : ℕ}
    (allocation : Allocation) (m : ℕ) :
    Fintype (ActualOrbit (K := K) (tick := tick) allocation m) := by
  haveI : Finite (ActualOrbit (K := K) (tick := tick) allocation m) :=
    Finite.of_injective pairOrbitProfile pairOrbitProfile_injective
  exact Fintype.ofFinite _

def basePopulationBound {K tick : ℕ} (allocation : Allocation) : ℕ :=
  ∑ c : Classes K tick, activeCounts allocation 1 c.1 c.2

def orbitDegree (K tick : ℕ) : ℕ :=
  2 * ∑ c : Classes K tick, 7 ^ activeHalfLength c.1

theorem card_letters {K tick : ℕ} (c : Classes K tick) :
    Fintype.card (Letters c) = 7 ^ activeHalfLength c.1 := by
  simp only [Letters, Fintype.card_fun, Fintype.card_fin]

theorem class_card_le {K tick : ℕ} (allocation : Allocation) (m : ℕ)
    (c : Classes K tick) :
    Fintype.card (Positions allocation m c) ≤
      basePopulationBound (K := K) (tick := tick) allocation * m := by
  have hc : activeCounts allocation 1 c.1 c.2 ≤
      basePopulationBound (K := K) (tick := tick) allocation := by
    unfold basePopulationBound
    exact Finset.single_le_sum
      (fun (d : Classes K tick) _ => Nat.zero_le (activeCounts allocation 1 d.1 d.2))
      (Finset.mem_univ c)
  simp only [Positions, JointCanonicalization.ClassPositions, Fintype.card_fin,
    activeCounts_dilation allocation m]
  simpa only [Nat.mul_comm] using Nat.mul_le_mul_left m hc

theorem card_actualOrbit_le {K tick : ℕ} (allocation : Allocation) (m : ℕ) :
    Nat.card (ActualOrbit (K := K) (tick := tick) allocation m) ≤
      (basePopulationBound (K := K) (tick := tick) allocation * m + 1) ^
        orbitDegree K tick := by
  simpa only [ActualOrbit, orbitDegree, card_letters, two_mul] using
    (card_pairOrbits_le_common_bound
      (P := Positions (K := K) (tick := tick) allocation m)
      (X := Letters (K := K) (tick := tick))
      (Y := Letters (K := K) (tick := tick))
      (basePopulationBound (K := K) (tick := tick) allocation * m)
      (class_card_le allocation m))

theorem card_actualOrbit_le_polynomial {K tick : ℕ}
    (allocation : Allocation) (m : ℕ) :
    Nat.card (ActualOrbit (K := K) (tick := tick) allocation m) ≤
      (basePopulationBound (K := K) (tick := tick) allocation + 1) ^ orbitDegree K tick *
        (m + 1) ^ orbitDegree K tick := by
  refine (card_actualOrbit_le allocation m).trans ?_
  rw [← mul_pow]
  apply Nat.pow_le_pow_left
  nlinarith [Nat.zero_le (basePopulationBound (K := K) (tick := tick) allocation)]

def orbitPrefactor {K tick : ℕ} (allocation : Allocation) : ℝ :=
  ((basePopulationBound (K := K) (tick := tick) allocation + 1 : ℕ) : ℝ) ^
    orbitDegree K tick

theorem orbitPrefactor_pos {K tick : ℕ} (allocation : Allocation) :
    0 < orbitPrefactor (K := K) (tick := tick) allocation := by
  unfold orbitPrefactor
  positivity

theorem card_actualOrbit_le_polynomial_real {K tick : ℕ}
    (allocation : Allocation) (m : ℕ) :
    (Nat.card (ActualOrbit (K := K) (tick := tick) allocation m) : ℝ) ≤
      orbitPrefactor (K := K) (tick := tick) allocation *
        ((m : ℝ) + 1) ^ orbitDegree K tick := by
  unfold orbitPrefactor
  exact_mod_cast card_actualOrbit_le_polynomial (K := K) (tick := tick) allocation m

theorem usedOrbits_card_le {K tick : ℕ} (allocation : Allocation) (m : ℕ)
    (s : Finset (ActualOrbit (K := K) (tick := tick) allocation m)) :
    s.card ≤ (basePopulationBound (K := K) (tick := tick) allocation + 1) ^
      orbitDegree K tick * (m + 1) ^ orbitDegree K tick := by
  have hs : s.card ≤ Nat.card (ActualOrbit (K := K) (tick := tick) allocation m) := by
    rw [Nat.card_eq_fintype_card]
    exact s.card_le_univ
  exact hs.trans (card_actualOrbit_le_polynomial allocation m)

theorem usedOrbits_card_le_real {K tick : ℕ} (allocation : Allocation) (m : ℕ)
    (s : Finset (ActualOrbit (K := K) (tick := tick) allocation m)) :
    (s.card : ℝ) ≤ orbitPrefactor (K := K) (tick := tick) allocation *
      ((m : ℝ) + 1) ^ orbitDegree K tick := by
  unfold orbitPrefactor
  exact_mod_cast usedOrbits_card_le allocation m s

theorem taggedUsedOrbits_card_le_real {K tick : ℕ} (allocation : Allocation) (m : ℕ)
    (s : Finset (Fin 3 × ActualOrbit (K := K) (tick := tick) allocation m)) :
    (s.card : ℝ) ≤ (3 * orbitPrefactor (K := K) (tick := tick) allocation) *
      ((m : ℝ) + 1) ^ orbitDegree K tick := by
  have hs : s.card ≤ 3 * Nat.card
      (ActualOrbit (K := K) (tick := tick) allocation m) := by
    simpa only [Fintype.card_prod, Fintype.card_fin, Nat.card_eq_fintype_card] using
      s.card_le_univ
  have hsreal : (s.card : ℝ) ≤ 3 * (Nat.card
      (ActualOrbit (K := K) (tick := tick) allocation m) : ℝ) := by
    exact_mod_cast hs
  calc
    _ ≤ 3 * (Nat.card (ActualOrbit (K := K) (tick := tick) allocation m) : ℝ) := hsreal
    _ ≤ 3 * (orbitPrefactor (K := K) (tick := tick) allocation *
        ((m : ℝ) + 1) ^ orbitDegree K tick) :=
      mul_le_mul_of_nonneg_left (card_actualOrbit_le_polynomial_real allocation m)
        (by norm_num)
    _ = _ := (mul_assoc _ _ _).symm

end MatrixMultiplication.AllFieldHistoryOrbitCount

end
end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section

namespace MatrixMultiplication.AllFieldGroupOrbitCount

open AllFieldHistory AllFieldHistorySupport PermutationMatching
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq

abbrev GroupClasses (K tick : ℕ) (sigma : Placement) :=
  ActiveOrder K tick sigma × JointPopulation.Shape

abbrev GroupPositions {K tick : ℕ} (allocation : Allocation) (m : ℕ)
    {sigma : Placement} (c : GroupClasses K tick sigma) :=
  Fin (activeCounts allocation m c.1.val c.2)

abbrev GroupLetters {K tick : ℕ} {sigma : Placement} (c : GroupClasses K tick sigma) :=
  Fin (activeHalfLength c.1.val) → Fin 7

abbrev GroupOrbit {K tick : ℕ} (allocation : Allocation) (m : ℕ) (sigma : Placement) :=
  PairOrbit (GroupPositions (K := K) (tick := tick) (sigma := sigma) allocation m)
    (GroupLetters (K := K) (tick := tick) (sigma := sigma))
    (GroupLetters (K := K) (tick := tick) (sigma := sigma))

noncomputable instance groupOrbitFintype {K tick : ℕ}
    (allocation : Allocation) (m : ℕ) (sigma : Placement) :
    Fintype (GroupOrbit (K := K) (tick := tick) allocation m sigma) := by
  haveI : Finite (GroupOrbit (K := K) (tick := tick) allocation m sigma) :=
    Finite.of_injective pairOrbitProfile pairOrbitProfile_injective
  exact Fintype.ofFinite _

def groupDegree (K tick : ℕ) (sigma : Placement) : ℕ :=
  2 * ∑ c : GroupClasses K tick sigma, 7 ^ activeHalfLength c.1.val

theorem card_groupLetters {K tick : ℕ} {sigma : Placement}
    (c : GroupClasses K tick sigma) :
    Fintype.card (GroupLetters c) = 7 ^ activeHalfLength c.1.val := by
  simp only [GroupLetters, Fintype.card_fun, Fintype.card_fin]

theorem groupClass_card_le {K tick : ℕ} (allocation : Allocation) (m : ℕ)
    {sigma : Placement} (c : GroupClasses K tick sigma) :
    Fintype.card (GroupPositions allocation m c) ≤
      AllFieldHistoryOrbitCount.basePopulationBound (K := K) (tick := tick) allocation * m :=
  AllFieldHistoryOrbitCount.class_card_le allocation m (c.1.val, c.2)

theorem card_groupOrbit_le {K tick : ℕ}
    (allocation : Allocation) (m : ℕ) (sigma : Placement) :
    Nat.card (GroupOrbit (K := K) (tick := tick) allocation m sigma) ≤
      (AllFieldHistoryOrbitCount.basePopulationBound (K := K) (tick := tick) allocation * m + 1) ^
        groupDegree K tick sigma := by
  simpa only [GroupOrbit, groupDegree, card_groupLetters, two_mul] using
    (card_pairOrbits_le_common_bound
      (P := GroupPositions (K := K) (tick := tick) (sigma := sigma) allocation m)
      (X := GroupLetters (K := K) (tick := tick) (sigma := sigma))
      (Y := GroupLetters (K := K) (tick := tick) (sigma := sigma))
      (AllFieldHistoryOrbitCount.basePopulationBound (K := K) (tick := tick) allocation * m)
      (groupClass_card_le allocation m))

theorem card_groupOrbit_le_polynomial {K tick : ℕ}
    (allocation : Allocation) (m : ℕ) (sigma : Placement) :
    Nat.card (GroupOrbit (K := K) (tick := tick) allocation m sigma) ≤
      (AllFieldHistoryOrbitCount.basePopulationBound (K := K) (tick := tick) allocation + 1) ^
        groupDegree K tick sigma * (m + 1) ^ groupDegree K tick sigma := by
  refine (card_groupOrbit_le allocation m sigma).trans ?_
  rw [← mul_pow]
  apply Nat.pow_le_pow_left
  nlinarith [Nat.zero_le
    (AllFieldHistoryOrbitCount.basePopulationBound (K := K) (tick := tick) allocation)]

def groupOrbitPrefactor {K tick : ℕ} (allocation : Allocation) (sigma : Placement) : ℝ :=
  ((AllFieldHistoryOrbitCount.basePopulationBound (K := K) (tick := tick) allocation + 1 : ℕ) : ℝ) ^
    groupDegree K tick sigma

theorem groupOrbitPrefactor_pos {K tick : ℕ} (allocation : Allocation) (sigma : Placement) :
    0 < groupOrbitPrefactor (K := K) (tick := tick) allocation sigma := by
  unfold groupOrbitPrefactor
  positivity

theorem card_groupOrbit_le_polynomial_real {K tick : ℕ}
    (allocation : Allocation) (m : ℕ) (sigma : Placement) :
    (Nat.card (GroupOrbit (K := K) (tick := tick) allocation m sigma) : ℝ) ≤
      groupOrbitPrefactor (K := K) (tick := tick) allocation sigma *
        ((m : ℝ) + 1) ^ groupDegree K tick sigma := by
  unfold groupOrbitPrefactor
  exact_mod_cast card_groupOrbit_le_polynomial (K := K) (tick := tick) allocation m sigma

theorem usedGroupOrbits_card_le_real {K tick : ℕ} (allocation : Allocation) (m : ℕ)
    (sigma : Placement)
    (s : Finset (GroupOrbit (K := K) (tick := tick) allocation m sigma)) :
    (s.card : ℝ) ≤ groupOrbitPrefactor (K := K) (tick := tick) allocation sigma *
      ((m : ℝ) + 1) ^ groupDegree K tick sigma := by
  have hs : s.card ≤ Nat.card (GroupOrbit (K := K) (tick := tick) allocation m sigma) := by
    rw [Nat.card_eq_fintype_card]
    exact s.card_le_univ
  have hsreal : (s.card : ℝ) ≤
      (Nat.card (GroupOrbit (K := K) (tick := tick) allocation m sigma) : ℝ) := by
    exact_mod_cast hs
  exact hsreal.trans (card_groupOrbit_le_polynomial_real allocation m sigma)

theorem taggedUsedGroupOrbits_card_le_real {K tick : ℕ}
    (allocation : Allocation) (m : ℕ) (sigma : Placement)
    (s : Finset (Fin 3 × GroupOrbit (K := K) (tick := tick) allocation m sigma)) :
    (s.card : ℝ) ≤ (3 * groupOrbitPrefactor (K := K) (tick := tick) allocation sigma) *
      ((m : ℝ) + 1) ^ groupDegree K tick sigma := by
  have hs : s.card ≤ 3 * Nat.card
      (GroupOrbit (K := K) (tick := tick) allocation m sigma) := by
    simpa only [Fintype.card_prod, Fintype.card_fin, Nat.card_eq_fintype_card] using
      s.card_le_univ
  have hsreal : (s.card : ℝ) ≤ 3 * (Nat.card
      (GroupOrbit (K := K) (tick := tick) allocation m sigma) : ℝ) := by
    exact_mod_cast hs
  calc
    _ ≤ 3 * (Nat.card (GroupOrbit (K := K) (tick := tick) allocation m sigma) : ℝ) := hsreal
    _ ≤ 3 * (groupOrbitPrefactor (K := K) (tick := tick) allocation sigma *
        ((m : ℝ) + 1) ^ groupDegree K tick sigma) :=
      mul_le_mul_of_nonneg_left (card_groupOrbit_le_polynomial_real allocation m sigma)
        (by norm_num)
    _ = _ := (mul_assoc _ _ _).symm

end MatrixMultiplication.AllFieldGroupOrbitCount

end
end

end MatrixAllFields

end OAI
