import OAI.Analysis.PlanarEndpoint.Information.FiniteTables
import OAI.Analysis.PlanarEndpoint.Information.Logarithms

namespace OAI

/-! Finite information laws, entropy and convergence of probability measures. -/


noncomputable section
open scoped BigOperators
namespace PlanarEndpoint.TransverseInformation

lemma neg_mul_log_le_two_sqrt {p : ℝ} (hp : 0 ≤ p) :
    -p * Real.log p ≤ 2 * Real.sqrt p := by
  by_cases hp0 : p = 0
  · simp only [hp0, neg_zero, zero_mul, Real.sqrt_zero, mul_zero, le_refl]
  have hp' : 0 < p := lt_of_le_of_ne hp (Ne.symm hp0)
  have hs : 0 < Real.sqrt p := Real.sqrt_pos.mpr hp'
  have hlog := Real.log_le_sub_one_of_pos (inv_pos.mpr hs)
  rw [Real.log_inv, Real.log_sqrt hp] at hlog
  have hmul := mul_le_mul_of_nonneg_left hlog (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hp)
  have hid : p * (Real.sqrt p)⁻¹ = Real.sqrt p := by
    calc
      p * (Real.sqrt p)⁻¹ = ((Real.sqrt p) * (Real.sqrt p)) * (Real.sqrt p)⁻¹ := by
        rw [← pow_two, Real.sq_sqrt hp]
      _ = Real.sqrt p := by rw [mul_assoc, mul_inv_cancel₀ hs.ne', mul_one]
  calc
    -p * Real.log p = (2 * p) * (-(Real.log p / 2)) := by ring
    _ ≤ (2 * p) * ((Real.sqrt p)⁻¹ - 1) := hmul
    _ = 2 * Real.sqrt p - 2 * p := by rw [mul_sub, mul_one, mul_assoc, hid]
    _ ≤ 2 * Real.sqrt p := by linarith

lemma information_tail_pointwise {L p A : ℝ} (hL : 1 < L) (hp : 0 ≤ p) :
    (if A < information L p then p * information L p else 0) ≤
        (2 / Real.log L) * Real.sqrt (L ^ (-A)) := by
  classical
  have hL0 : 0 < L := lt_trans zero_lt_one hL
  have hl : 0 < Real.log L := Real.log_pos hL
  have hr : 0 ≤ (2 / Real.log L) * Real.sqrt (L ^ (-A)) :=
    mul_nonneg (div_nonneg (by norm_num) hl.le) (Real.sqrt_nonneg _)
  by_cases hp0 : p = 0
  · simp only [hp0, zero_mul, ite_self]
    exact hr
  have hp' : 0 < p := lt_of_le_of_ne hp (Ne.symm hp0)
  split_ifs with h
  · have hsmall := (information_gt_iff hL hp').mp h
    calc
      p * information L p = (-p * Real.log p) / Real.log L := by
        unfold information
        ring
      _ ≤ (2 * Real.sqrt p) / Real.log L :=
        div_le_div_of_nonneg_right (neg_mul_log_le_two_sqrt hp) hl.le
      _ = (2 / Real.log L) * Real.sqrt p := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hsmall.le)
        (div_nonneg (by norm_num) hl.le)
  · exact hr

lemma information_mass_tail_le {Y : Type*} [Fintype Y]
    (p : Y → ℝ) (hp : ∀ y, 0 ≤ p y) {L A : ℝ} (hL : 1 < L) :
    (∑ y, if A < information L (p y) then p y else 0) ≤
      (Fintype.card Y : ℝ) * L ^ (-A) := by
  classical
  calc
    _ ≤ ∑ _y : Y, L ^ (-A) := by
      apply Finset.sum_le_sum
      intro y _
      by_cases hp0 : p y = 0
      · simp only [hp0, ite_self]
        exact Real.rpow_nonneg (by linarith) _
      have hp' : 0 < p y := lt_of_le_of_ne (hp y) (Ne.symm hp0)
      split_ifs with h
      · exact ((information_gt_iff hL hp').mp h).le
      · exact Real.rpow_nonneg (by linarith) _
    _ = _ := by simp

lemma information_expected_tail_le {Y : Type*} [Fintype Y]
    (p : Y → ℝ) (hp : ∀ y, 0 ≤ p y) {L A : ℝ} (hL : 1 < L) :
    (∑ y, if A < information L (p y) then p y * information L (p y) else 0) ≤
      (Fintype.card Y : ℝ) * (2 / Real.log L) * Real.sqrt (L ^ (-A)) := by
  classical
  calc
    _ ≤ ∑ _y : Y, (2 / Real.log L) * Real.sqrt (L ^ (-A)) :=
      Finset.sum_le_sum (fun y _ => information_tail_pointwise hL (hp y))
    _ = _ := by simp [mul_assoc]

lemma jointMass_eq_row_mul_conditional {V Y : Type*} [Fintype V] [Fintype Y]
    (q : V → Y → ℝ) (hq : ∀ v y, 0 ≤ q v y) (v : V) (y : Y) :
    q v y = rowMass q v * conditionalMass q v y := by
  by_cases hv : rowMass q v = 0
  · have hq0 : q v y = 0 := le_antisymm (by simpa [hv] using le_rowMass q hq v y) (hq v y)
    simp [hv, hq0]
  · unfold conditionalMass
    field_simp

lemma conditional_information_nonneg {V Y : Type*} [Fintype V] [Fintype Y]
    (q : V → Y → ℝ) (hq : ∀ v y, 0 ≤ q v y) {L : ℝ} (hL : 1 < L)
    (v : V) (y : Y) : 0 ≤ information L (conditionalMass q v y) := by
  have hp0 : 0 ≤ conditionalMass q v y :=
    div_nonneg (hq v y) (rowMass_nonneg q hq v)
  have hp1 : conditionalMass q v y ≤ 1 := by
    by_cases hr : rowMass q v = 0
    · simp [conditionalMass, hr]
    · exact (div_le_one (lt_of_le_of_ne (rowMass_nonneg q hq v) (Ne.symm hr))).mpr
        (le_rowMass q hq v y)
  exact div_nonneg (neg_nonneg.mpr (Real.log_nonpos hp0 hp1)) (Real.log_pos hL).le

lemma conditional_information_mass_tail_le {V Y : Type*} [Fintype V] [Fintype Y]
    (q : V → Y → ℝ) (hq : ∀ v y, 0 ≤ q v y)
    (hq1 : ∑ v, ∑ y, q v y = 1) {L A : ℝ} (hL : 1 < L) :
    (∑ v, ∑ y, if A < information L (conditionalMass q v y) then q v y else 0) ≤
      (Fintype.card Y : ℝ) * L ^ (-A) := by
  classical
  have hc : ∀ v y, 0 ≤ conditionalMass q v y := fun v y =>
    div_nonneg (hq v y) (rowMass_nonneg q hq v)
  calc
    _ = ∑ v, rowMass q v * (∑ y, if A < information L (conditionalMass q v y)
        then conditionalMass q v y else 0) := by
      apply Finset.sum_congr rfl
      intro v _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro y _
      split_ifs
      · exact jointMass_eq_row_mul_conditional q hq v y
      · simp
    _ ≤ ∑ v, rowMass q v * ((Fintype.card Y : ℝ) * L ^ (-A)) := by
      apply Finset.sum_le_sum
      intro v _
      exact mul_le_mul_of_nonneg_left
        (information_mass_tail_le (conditionalMass q v) (hc v) hL)
        (rowMass_nonneg q hq v)
    _ = _ := by
      rw [← Finset.sum_mul]
      simp only [rowMass, hq1, one_mul]

lemma conditional_information_expected_tail_le {V Y : Type*} [Fintype V] [Fintype Y]
    (q : V → Y → ℝ) (hq : ∀ v y, 0 ≤ q v y)
    (hq1 : ∑ v, ∑ y, q v y = 1) {L A : ℝ} (hL : 1 < L) :
    (∑ v, ∑ y, if A < information L (conditionalMass q v y) then
      q v y * information L (conditionalMass q v y) else 0) ≤
      (Fintype.card Y : ℝ) * (2 / Real.log L) * Real.sqrt (L ^ (-A)) := by
  classical
  have hc : ∀ v y, 0 ≤ conditionalMass q v y := fun v y =>
    div_nonneg (hq v y) (rowMass_nonneg q hq v)
  calc
    _ = ∑ v, rowMass q v * (∑ y, if A < information L (conditionalMass q v y)
        then conditionalMass q v y * information L (conditionalMass q v y) else 0) := by
      apply Finset.sum_congr rfl
      intro v _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro y _
      split_ifs
      · rw [← mul_assoc, ← jointMass_eq_row_mul_conditional q hq]
      · simp
    _ ≤ ∑ v, rowMass q v * ((Fintype.card Y : ℝ) * (2 / Real.log L) *
        Real.sqrt (L ^ (-A))) := by
      apply Finset.sum_le_sum
      intro v _
      exact mul_le_mul_of_nonneg_left
        (information_expected_tail_le (conditionalMass q v) (hc v) hL)
        (rowMass_nonneg q hq v)
    _ = _ := by
      rw [← Finset.sum_mul]
      simp only [rowMass, hq1, one_mul]

lemma polynomial_alphabet_tail_bound {n : ℕ} {L C A : ℝ}
    (hL : 2 ≤ L) (hn : (n : ℝ) ≤ L ^ C) (hA : 2 * C ≤ A) :
    (n : ℝ) * (2 / Real.log L) * Real.sqrt (L ^ (-A)) ≤
      (2 / Real.log 2) * (2 : ℝ) ^ (C - A / 2) := by
  have hL0 : 0 < L := by linarith
  have hl : 0 < Real.log L := Real.log_pos (by linarith)
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hs : Real.sqrt (L ^ (-A)) = L ^ (-A / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hL0.le]
    congr 1
    ring
  rw [hs]
  calc
    _ ≤ (L ^ C) * (2 / Real.log L) * (L ^ (-A / 2)) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hn (div_nonneg (by norm_num) hl.le))
        (Real.rpow_nonneg hL0.le _)
    _ = (2 / Real.log L) * (L ^ (C - A / 2)) := by
      rw [sub_eq_add_neg, Real.rpow_add hL0, neg_div]
      ring
    _ ≤ (2 / Real.log 2) * (2 : ℝ) ^ (C - A / 2) := by
      apply mul_le_mul
      · exact div_le_div_of_nonneg_left (by norm_num) hl2 (Real.log_le_log (by norm_num) hL)
      · exact Real.rpow_le_rpow_of_nonpos (by norm_num) hL (by linarith)
      · exact Real.rpow_nonneg hL0.le _
      · exact div_nonneg (by norm_num) hl2.le

lemma polynomial_alphabet_mass_bound {n : ℕ} {L C A : ℝ}
    (hL : 2 ≤ L) (hn : (n : ℝ) ≤ L ^ C) (hA : C ≤ A) :
    (n : ℝ) * L ^ (-A) ≤ (2 : ℝ) ^ (C - A) := by
  have hL0 : 0 < L := by linarith
  calc
    _ ≤ L ^ C * L ^ (-A) :=
      mul_le_mul_of_nonneg_right hn (Real.rpow_nonneg hL0.le _)
    _ = L ^ (C-A) := by rw [sub_eq_add_neg, Real.rpow_add hL0]
    _ ≤ _ := Real.rpow_le_rpow_of_nonpos (by norm_num) hL (sub_nonpos.mpr hA)

open Filter in
lemma polynomial_alphabet_mass_envelope_tendsto_zero (C : ℝ) :
    Tendsto (fun A : ℝ => (2 : ℝ) ^ (C-A)) atTop (nhds 0) := by
  have ht : Tendsto (fun A : ℝ => C-A) atTop atBot := by
    apply tendsto_atBot.mpr
    intro b
    filter_upwards [eventually_ge_atTop (C-b)] with A hA
    linarith
  exact (tendsto_rpow_atBot_of_base_gt_one 2 (by norm_num)).comp ht

open Filter in
lemma polynomial_alphabet_envelope_tendsto_zero (C : ℝ) :
    Tendsto (fun A : ℝ => (2 / Real.log 2) * (2 : ℝ) ^ (C - A / 2))
      atTop (nhds 0) := by
  have ht : Tendsto (fun A : ℝ => C - A / 2) atTop atBot := by
    apply tendsto_atBot.mpr
    intro b
    filter_upwards [eventually_ge_atTop (2 * (C-b))] with A hA
    linarith
  simpa only [Function.comp_def, mul_zero] using
    ((tendsto_rpow_atBot_of_base_gt_one 2 (by norm_num)).comp ht).const_mul (2 / Real.log 2)

lemma conditional_information_uniform_tail (C : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ A₀ : ℝ, ∀ A : ℝ, A₀ ≤ A →
      ∀ (V Y : Type) [Fintype V] [Fintype Y] (q : V → Y → ℝ),
      (∀ v y, 0 ≤ q v y) → (∑ v, ∑ y, q v y = 1) →
      ∀ L : ℝ, 2 ≤ L → (Fintype.card Y : ℝ) ≤ L ^ C →
      (∑ v, ∑ y, if A < information L (conditionalMass q v y) then
        q v y * information L (conditionalMass q v y) else 0) < ε := by
  classical
  have he := (polynomial_alphabet_envelope_tendsto_zero C).eventually
    (gt_mem_nhds hε)
  obtain ⟨a, ha⟩ := Filter.eventually_atTop.mp he
  refine ⟨max a (2*C), fun A hA V Y _ _ q hq hq1 L hL hn => ?_⟩
  exact ((conditional_information_expected_tail_le q hq hq1 (by linarith)).trans
    (polynomial_alphabet_tail_bound hL hn ((le_max_right _ _).trans hA))).trans_lt
      (ha A ((le_max_left _ _).trans hA))

end PlanarEndpoint.TransverseInformation
end

end OAI
