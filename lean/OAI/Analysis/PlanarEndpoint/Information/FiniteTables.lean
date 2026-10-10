import OAI.Analysis.PlanarEndpoint.Information.Logarithms

namespace OAI

/-! Finite information laws, entropy and convergence of probability measures. -/


noncomputable section
open scoped BigOperators
open Finset
namespace PlanarEndpoint.TransverseInformation

variable {V Y : Type*} [Fintype V] [Fintype Y]

def rowMass (q : V → Y → ℝ) (v : V) : ℝ := ∑ y, q v y
def colMass (q : V → Y → ℝ) (y : Y) : ℝ := ∑ v, q v y
def conditionalMass (q : V → Y → ℝ) (v : V) (y : Y) : ℝ :=
  q v y / rowMass q v

omit [Fintype V] in
lemma rowMass_nonneg (q : V → Y → ℝ) (hq : ∀ v y, 0 ≤ q v y) (v : V) :
    0 ≤ rowMass q v := Finset.sum_nonneg (fun y _ => hq v y)

omit [Fintype Y] in
lemma colMass_nonneg (q : V → Y → ℝ) (hq : ∀ v y, 0 ≤ q v y) (y : Y) :
    0 ≤ colMass q y := Finset.sum_nonneg (fun v _ => hq v y)

omit [Fintype V] in
lemma le_rowMass (q : V → Y → ℝ) (hq : ∀ v y, 0 ≤ q v y) (v : V) (y : Y) :
    q v y ≤ rowMass q v := Finset.single_le_sum (fun z _ => hq v z) (Finset.mem_univ y)

omit [Fintype Y] in
lemma le_colMass (q : V → Y → ℝ) (hq : ∀ v y, 0 ≤ q v y) (v : V) (y : Y) :
    q v y ≤ colMass q y := Finset.single_le_sum (fun z _ => hq z y) (Finset.mem_univ v)

lemma conditional_information_chain {L a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    information L a = information L b + information L (a/b) := by
  unfold information
  rw [Real.log_div ha.ne' hb.ne']
  ring

omit [Fintype V] in
lemma joint_information_chain (q : V → Y → ℝ) (hq : ∀ v y, 0 ≤ q v y)
    {v : V} {y : Y} (h : 0 < q v y) (L : ℝ) :
    information L (q v y) = information L (rowMass q v) +
      information L (conditionalMass q v y) :=
  conditional_information_chain h (h.trans_le (le_rowMass q hq v y))

lemma joint_conditioning_exception_le (q : V → Y → ℝ)
    (hq : ∀ v y, 0 ≤ q v y) (hq1 : ∑ v, ∑ y, q v y = 1)
    {L η : ℝ} (hL : 1 < L) :
    (∑ v, ∑ y, if information L (colMass q y) -
        information L (conditionalMass q v y) < -η then q v y else 0)
      ≤ L ^ (-η) := by
  classical
  have hL0 : 0 < L := lt_trans zero_lt_one hL
  have hε : 0 ≤ L ^ (-η) := Real.rpow_nonneg hL0.le _
  have hcol : ∑ y, colMass q y = 1 := by
    change (∑ y, ∑ v, q v y) = 1
    rw [Finset.sum_comm]
    exact hq1
  calc
    _ ≤ ∑ v, ∑ y, L ^ (-η) * rowMass q v * colMass q y := by
      apply Finset.sum_le_sum
      intro v _
      apply Finset.sum_le_sum
      intro y _
      by_cases hqvy : q v y = 0
      · simp only [hqvy, ite_self]
        exact mul_nonneg (mul_nonneg hε (rowMass_nonneg q hq v))
          (colMass_nonneg q hq y)
      · have hvy : 0 < q v y := lt_of_le_of_ne (hq v y) (Ne.symm hqvy)
        have hv : 0 < rowMass q v := hvy.trans_le (le_rowMass q hq v y)
        have hy : 0 < colMass q y := hvy.trans_le (le_colMass q hq v y)
        split_ifs with h
        · have h' := (information_bad_iff hL hy (div_pos hvy hv)).mp h
          have h'' := (div_lt_iff₀ hv).mp h'
          nlinarith
        · exact mul_nonneg (mul_nonneg hε hv.le) hy.le
    _ = L ^ (-η) := by
      simp_rw [← Finset.mul_sum, hcol, mul_one]
      rw [← Finset.mul_sum]
      simp only [rowMass, hq1, mul_one]

lemma information_gt_iff {L p γ : ℝ} (hL : 1 < L) (hp : 0 < p) :
    γ < information L p ↔ p < L ^ (-γ) := by
  unfold information
  rw [lt_div_iff₀ (Real.log_pos hL)]
  have hL0 : 0 < L := lt_trans zero_lt_one hL
  constructor
  · intro h
    have : Real.log p < Real.log (L ^ (-γ)) := by
      rw [Real.log_rpow hL0]
      linarith
    exact (Real.log_lt_log_iff hp (Real.rpow_pos_of_pos hL0 _)).mp this
  · intro h
    have := Real.log_lt_log hp h
    rw [Real.log_rpow hL0] at this
    linarith

lemma conditional_determination_exception_le (q e : Y → ℝ) (S : Finset Y)
    (hq : ∀ y, 0 ≤ q y) (he : ∀ y, 0 ≤ e y ∧ e y ≤ q y)
    (hs : ∀ y, y ∉ S → e y = 0) {L γ : ℝ} (hL : 1 < L) :
    (∑ y, if γ < information L (q y / ∑ z, q z) then e y else 0)
      ≤ S.card * L ^ (-γ) * ∑ z, q z := by
  classical
  have hm : 0 ≤ ∑ z, q z := Finset.sum_nonneg (fun z _ => hq z)
  have hε : 0 ≤ L ^ (-γ) := Real.rpow_nonneg (by linarith) _
  calc
    _ = ∑ y ∈ S, if γ < information L (q y / ∑ z, q z) then e y else 0 := by
      symm
      apply Finset.sum_subset (Finset.subset_univ S)
      intro y _ hy
      simp only [hs y hy, ite_self]
    _ ≤ ∑ y ∈ S, L ^ (-γ) * ∑ z, q z := by
      apply Finset.sum_le_sum
      intro y hy
      by_cases he0 : e y = 0
      · simp only [he0, ite_self]
        exact mul_nonneg hε hm
      · have hey : 0 < e y := lt_of_le_of_ne (he y).1 (Ne.symm he0)
        have hqy : 0 < q y := hey.trans_le (he y).2
        have hmq : 0 < ∑ z, q z := hqy.trans_le
          (Finset.single_le_sum (fun z _ => hq z) (Finset.mem_univ y))
        split_ifs with h
        · have h' := (information_gt_iff hL (div_pos hqy hmq)).mp h
          exact (he y).2.trans ((div_lt_iff₀ hmq).mp h').le
        · exact mul_nonneg hε hm
    _ = _ := by simp [mul_assoc]

lemma sub_le_mul_log_div {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : 0 < a → 0 < b) : a - b ≤ a * Real.log (a / b) := by
  by_cases ha0 : a = 0
  · simp only [ha0, zero_sub, zero_mul]
    exact neg_nonpos.mpr hb
  · have ha' : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
    have hb' := hab ha'
    have hlog := Real.log_le_sub_one_of_pos (div_pos hb' ha')
    have hh := mul_le_mul_of_nonneg_left hlog ha
    rw [Real.log_div hb'.ne' ha0] at hh
    rw [Real.log_div ha0 hb'.ne']
    have hc : a * (b / a) = b := mul_div_cancel₀ b ha0
    nlinarith

lemma information_nonneg {L p : ℝ} (hL : 1 < L) (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    0 ≤ information L p := by
  unfold information
  apply div_nonneg _ (Real.log_pos hL).le
  exact neg_nonneg.mpr (Real.log_nonpos hp hp1)

lemma expected_conditioning_decrement_nonneg (q : V → Y → ℝ)
    (hq : ∀ v y, 0 ≤ q v y) (hq1 : ∑ v, ∑ y, q v y = 1)
    {L : ℝ} (hL : 1 < L) :
    0 ≤ ∑ v, ∑ y, q v y * (information L (colMass q y) -
      information L (conditionalMass q v y)) := by
  classical
  have hcol : ∑ y, colMass q y = 1 := by
    change (∑ y, ∑ v, q v y) = 1
    rw [Finset.sum_comm]
    exact hq1
  have hrow : ∑ v, rowMass q v = 1 := hq1
  have hsum : ∑ v, ∑ y, (q v y - rowMass q v * colMass q y) = 0 := by
    simp_rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hcol, mul_one]
    rw [hq1, hrow, sub_self]
  calc
    _ = ∑ v, ∑ y, (q v y - rowMass q v * colMass q y) / Real.log L := by
      simp_rw [← Finset.sum_div]
      rw [hsum, zero_div]
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro v _
      apply Finset.sum_le_sum
      intro y _
      by_cases hq0 : q v y = 0
      · simp only [hq0, zero_sub, zero_mul]
        exact div_nonpos_of_nonpos_of_nonneg
          (neg_nonpos.mpr (mul_nonneg (rowMass_nonneg q hq v) (colMass_nonneg q hq y)))
          (Real.log_pos hL).le
      · have hqy : 0 < q v y := lt_of_le_of_ne (hq v y) (Ne.symm hq0)
        have hr : 0 < rowMass q v := hqy.trans_le (le_rowMass q hq v y)
        have hc : 0 < colMass q y := hqy.trans_le (le_colMass q hq v y)
        have h := sub_le_mul_log_div (hq v y) (mul_nonneg hr.le hc.le)
          (fun _ => mul_pos hr hc)
        have h' := div_le_div_of_nonneg_right h (Real.log_pos hL).le
        unfold information conditionalMass
        rw [Real.log_div hq0 (mul_pos hr hc).ne', Real.log_mul hr.ne' hc.ne'] at h'
        rw [Real.log_div hq0 hr.ne']
        convert h' using 1
        ring

def entropy (L : ℝ) (p : Y → ℝ) : ℝ := ∑ y, p y * information L (p y)

def conditionalEntropy (L : ℝ) (q : V → Y → ℝ) : ℝ :=
  ∑ v, ∑ y, q v y * information L (conditionalMass q v y)

lemma expected_conditioning_decrement_eq (L : ℝ) (q : V → Y → ℝ) :
    (∑ v, ∑ y, q v y * (information L (colMass q y) -
      information L (conditionalMass q v y))) =
        entropy L (colMass q) - conditionalEntropy L q := by
  unfold entropy conditionalEntropy
  simp_rw [mul_sub, Finset.sum_sub_distrib]
  congr 1
  rw [Finset.sum_comm]
  simp only [colMass, Finset.sum_mul]

lemma entropy_conditioning_le (q : V → Y → ℝ)
    (hq : ∀ v y, 0 ≤ q v y) (hq1 : ∑ v, ∑ y, q v y = 1)
    {L : ℝ} (hL : 1 < L) :
    conditionalEntropy L q ≤ entropy L (colMass q) := by
  have h := expected_conditioning_decrement_nonneg q hq hq1 hL
  rw [expected_conditioning_decrement_eq] at h
  linarith

lemma conditionalEntropy_nonneg (q : V → Y → ℝ) (hq : ∀ v y, 0 ≤ q v y)
    {L : ℝ} (hL : 1 < L) : 0 ≤ conditionalEntropy L q := by
  apply Finset.sum_nonneg
  intro v _
  apply Finset.sum_nonneg
  intro y _
  apply mul_nonneg (hq v y)
  apply information_nonneg hL
  · exact div_nonneg (hq v y) (rowMass_nonneg q hq v)
  · unfold conditionalMass
    by_cases hr : rowMass q v = 0
    · simp only [hr, div_zero, zero_le_one]
    · apply (div_le_one (lt_of_le_of_ne (rowMass_nonneg q hq v) (Ne.symm hr))).mpr
      exact le_rowMass q hq v y

lemma entropy_nonneg (p : Y → ℝ) (hp : ∀ y, 0 ≤ p y) (hp1 : ∑ y, p y = 1)
    {L : ℝ} (hL : 1 < L) : 0 ≤ entropy L p := by
  apply Finset.sum_nonneg
  intro y _
  apply mul_nonneg (hp y) (information_nonneg hL (hp y) _)
  rw [← hp1]
  exact Finset.single_le_sum (fun z _ => hp z) (Finset.mem_univ y)

lemma entropy_joint_eq (L : ℝ) (q : V → Y → ℝ) (hq : ∀ v y, 0 ≤ q v y) :
    entropy L (fun vy : V × Y => q vy.1 vy.2) =
      entropy L (rowMass q) + conditionalEntropy L q := by
  classical
  unfold entropy conditionalEntropy
  rw [Fintype.sum_prod_type]
  calc
    _ = ∑ v, ∑ y, q v y * (information L (rowMass q v) +
        information L (conditionalMass q v y)) := by
      apply Finset.sum_congr rfl
      intro v _
      apply Finset.sum_congr rfl
      intro y _
      by_cases hq0 : q v y = 0
      · simp only [hq0, zero_mul]
      · rw [joint_information_chain q hq (lt_of_le_of_ne (hq v y) (Ne.symm hq0)) L]
    _ = _ := by
      simp_rw [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul]
      rfl

lemma entropy_joint_swap (L : ℝ) (q : V → Y → ℝ) :
    entropy L (fun vy : V × Y => q vy.1 vy.2) =
      entropy L (fun yv : Y × V => q yv.2 yv.1) := by
  unfold entropy
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type, Finset.sum_comm]

lemma conditioning_decrement_le_label_entropy (q : V → Y → ℝ)
    (hq : ∀ v y, 0 ≤ q v y) {L : ℝ} (hL : 1 < L) :
    entropy L (colMass q) - conditionalEntropy L q ≤ entropy L (rowMass q) := by
  have h1 := entropy_joint_eq L q hq
  have h2 := entropy_joint_eq L (fun y v => q v y) (fun y v => hq v y)
  rw [← entropy_joint_swap L q] at h2
  have h3 := conditionalEntropy_nonneg (fun y v => q v y) (fun y v => hq v y) hL
  change entropy L (fun vy : V × Y => q vy.1 vy.2) =
    entropy L (colMass q) + conditionalEntropy L (fun y v => q v y) at h2
  linarith

lemma entropy_le_log_card (p : Y → ℝ) (hp : ∀ y, 0 ≤ p y) (hp1 : ∑ y, p y = 1)
    {L : ℝ} (hL : 1 < L) :
    entropy L p ≤ Real.log (Fintype.card Y) / Real.log L := by
  classical
  have hnonempty : Nonempty Y := by
    by_contra h
    let : IsEmpty Y := not_nonempty_iff.mp h
    simp only [Finset.univ_eq_empty, Finset.sum_empty] at hp1
    norm_num at hp1
  let : Nonempty Y := hnonempty
  have hn : 0 < (Fintype.card Y : ℝ) := Nat.cast_pos.mpr Fintype.card_pos
  have hu : 0 < (Fintype.card Y : ℝ)⁻¹ := inv_pos.mpr hn
  have hsum : ∑ y, (p y - (Fintype.card Y : ℝ)⁻¹) = 0 := by
    rw [Finset.sum_sub_distrib, hp1]
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_inv_cancel₀ hn.ne', sub_self]
  have hbound : 0 ≤ ∑ y, p y * Real.log (p y / (Fintype.card Y : ℝ)⁻¹) := by
    rw [← hsum]
    exact Finset.sum_le_sum (fun y _ => sub_le_mul_log_div (hp y) hu.le (fun _ => hu))
  have hid : (∑ y, p y * Real.log (p y / (Fintype.card Y : ℝ)⁻¹)) =
      (∑ y, p y * Real.log (p y)) + Real.log (Fintype.card Y) := by
    calc
      _ = ∑ y, (p y * Real.log (p y) + p y * Real.log (Fintype.card Y)) := by
        apply Finset.sum_congr rfl
        intro y _
        by_cases hp0 : p y = 0
        · simp only [hp0, zero_mul, add_zero]
        · rw [Real.log_div hp0 hu.ne', Real.log_inv]
          ring
      _ = _ := by rw [Finset.sum_add_distrib, ← Finset.sum_mul, hp1, one_mul]
  rw [hid] at hbound
  unfold entropy information
  have heq : (∑ y, p y * (-Real.log (p y) / Real.log L)) =
      -(∑ y, p y * Real.log (p y)) / Real.log L := by
    simp_rw [← mul_div_assoc, mul_neg, ← Finset.sum_div, Finset.sum_neg_distrib]
  rw [heq]
  exact div_le_div_of_nonneg_right (by linarith) (Real.log_pos hL).le

lemma direction_bin_cost_bound (q : V → Y → ℝ)
    (hq : ∀ v y, 0 ≤ q v y) (hq1 : ∑ v, ∑ y, q v y = 1)
    {L : ℝ} (hL : 1 < L) :
    0 ≤ entropy L (colMass q) - conditionalEntropy L q ∧
    entropy L (colMass q) - conditionalEntropy L q ≤
      Real.log (Fintype.card V) / Real.log L := by
  constructor
  · exact sub_nonneg.mpr (entropy_conditioning_le q hq hq1 hL)
  · exact (conditioning_decrement_le_label_entropy q hq hL).trans
      (entropy_le_log_card (rowMass q) (rowMass_nonneg q hq) hq1 hL)

end PlanarEndpoint.TransverseInformation
end

end OAI
