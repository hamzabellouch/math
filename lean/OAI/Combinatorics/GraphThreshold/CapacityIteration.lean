import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Algebra.Order.Field.GeomSum
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Order.Interval.Set.Monotone
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace OAI

/-!
# Capacities and finite inflation products

The capacity after `t` successful reductions is natural-number division by
`2^t`. All product estimates below are finite; no infinite product is used.
-/

noncomputable section

open Finset Set

namespace LeanBlast.SecondKahnKalai

def reducedCapacity (l t : ℕ) : ℕ := l / 2 ^ t

def successesNeeded (l : ℕ) : ℕ := Nat.log2 l + 1

@[simp] theorem reducedCapacity_zero (l : ℕ) : reducedCapacity l 0 = l := by
  simp [reducedCapacity]

theorem reducedCapacity_succ (l t : ℕ) :
    reducedCapacity l (t + 1) = reducedCapacity l t / 2 := by
  simp only [reducedCapacity, pow_succ, Nat.div_div_eq_div_mul]

theorem reducedCapacity_add (l t u : ℕ) :
    reducedCapacity l (t + u) = reducedCapacity (reducedCapacity l t) u := by
  simp only [reducedCapacity, pow_add, Nat.div_div_eq_div_mul]

theorem reducedCapacity_eq_floor (l t : ℕ) :
    reducedCapacity l t = ⌊(l : ℝ) / (2 : ℝ) ^ t⌋₊ := by
  simpa only [reducedCapacity, Nat.cast_pow, Nat.cast_ofNat] using
    (Nat.floor_div_eq_div (K := ℝ) l (2 ^ t)).symm

theorem antitone_reducedCapacity (l : ℕ) : Antitone (reducedCapacity l) := by
  apply antitone_nat_of_succ_le
  intro t
  rw [reducedCapacity_succ]
  exact Nat.div_le_self _ _

theorem monotone_reducedCapacity_left (t : ℕ) : Monotone (fun l => reducedCapacity l t) := by
  intro a b hab
  exact Nat.div_le_div_right hab

theorem reducedCapacity_zero_prefix {a b t : ℕ} (hab : a ≤ b)
    (hb : reducedCapacity b t = 0) : reducedCapacity a t = 0 := by
  have h := monotone_reducedCapacity_left t hab
  change reducedCapacity a t ≤ reducedCapacity b t at h
  rw [hb] at h
  exact Nat.eq_zero_of_le_zero h

theorem reducedCapacity_growth {a b : ℕ} (hab : 16 * a ≤ b) (t : ℕ) :
    16 * reducedCapacity a t ≤ reducedCapacity b t := by
  unfold reducedCapacity
  apply (Nat.le_div_iff_mul_le (by positivity : 0 < 2 ^ t)).mpr
  calc
    16 * (a / 2 ^ t) * 2 ^ t = 16 * (a / 2 ^ t * 2 ^ t) := by ring
    _ ≤ 16 * a := Nat.mul_le_mul_left 16 (Nat.div_mul_le_self a (2 ^ t))
    _ ≤ b := hab

theorem strictAntiOn_reducedCapacity {l t : ℕ} (hpos : 0 < reducedCapacity l t) :
    StrictAntiOn (reducedCapacity l) (Set.Iic t) := by
  apply strictAntiOn_Iic_of_succ_lt
  intro u hu
  change reducedCapacity l (u + 1) < reducedCapacity l u
  rw [reducedCapacity_succ]
  exact Nat.div_lt_self (lt_of_lt_of_le hpos (antitone_reducedCapacity l hu.le)) (by decide)

theorem reducedCapacity_successesNeeded (l : ℕ) :
    reducedCapacity l (successesNeeded l) = 0 := by
  exact Nat.div_eq_of_lt Nat.lt_log2_self

theorem reducedCapacity_eq_zero_of_le {a l : ℕ} (hal : a ≤ l) :
    reducedCapacity a (successesNeeded l) = 0 := by
  exact Nat.div_eq_of_lt (lt_of_le_of_lt hal Nat.lt_log2_self)

theorem successesNeeded_pos (l : ℕ) : 0 < successesNeeded l := by
  exact Nat.succ_pos _

theorem monotone_successesNeeded : Monotone successesNeeded := by
  intro a b hab
  simp only [successesNeeded, Nat.log2_eq_log_two, Nat.add_le_add_iff_right]
  exact Nat.log_mono_right hab

theorem successesNeeded_half_lt {m : ℕ} (hhalf : 0 < m / 2) :
    successesNeeded (m / 2) < successesNeeded m := by
  have hm : 2 ≤ m := by omega
  have hl : Nat.log2 m = Nat.log2 (m / 2) + 1 := by
    rw [Nat.log2_def m, ite_eq_left hm]
  simp only [successesNeeded]
  omega

theorem successesNeeded_eq_floor_logb (l : ℕ) :
    successesNeeded l = ⌊Real.logb 2 (l : ℝ)⌋₊ + 1 := by
  simpa only [successesNeeded, Nat.log2_eq_log_two, Nat.cast_ofNat] using
    congrArg (fun n : ℕ => n + 1) (Real.natFloor_logb_natCast 2 l).symm

theorem successesNeeded_le_logb (l : ℕ) :
    (successesNeeded l : ℝ) ≤ 1 + Real.logb 2 (l : ℝ) := by
  have h := Real.log2_le_logb l
  simp only [successesNeeded, Nat.cast_add, Nat.cast_one]
  linarith

theorem capacity_logb_nonneg {l : ℕ} (hl : 1 ≤ l) :
    0 ≤ Real.logb 2 (l : ℝ) :=
  Real.logb_nonneg (by norm_num) (by exact_mod_cast hl)

theorem label_empty_after_successes {X : Type*} (A : Finset X) {l L : ℕ}
    (hl : l ≤ L) (hA : A.card ≤ reducedCapacity l (successesNeeded L)) : A = ∅ := by
  rw [reducedCapacity_eq_zero_of_le hl] at hA
  exact Finset.card_eq_zero.mp (Nat.eq_zero_of_le_zero hA)

/-- Geometric growth bounds every earlier prefix by one fifteenth of the
current capacity. The natural form avoids premature division. -/
theorem capacity_prefix_sum_le (m : ℕ → ℕ) (k : ℕ)
    (hgrowth : ∀ j, j + 1 < k → 16 * m j ≤ m (j + 1)) :
    ∀ j, j < k → 15 * (∑ h ∈ range j, m h) ≤ m j := by
  intro j
  induction j with
  | zero => simp
  | succ j ih =>
      intro hj
      have hp := ih (by omega)
      have hn := hgrowth j hj
      rw [sum_range_succ]
      omega

theorem capacity_prefix_sum_real_le (m : ℕ → ℕ) (k : ℕ)
    (hgrowth : ∀ j, j + 1 < k → 16 * m j ≤ m (j + 1))
    {j : ℕ} (hj : j < k) :
    (∑ h ∈ range j, (m h : ℝ)) ≤ (m j : ℝ) / 15 := by
  have h : (15 : ℝ) * (∑ h ∈ range j, (m h : ℝ)) ≤ (m j : ℝ) := by
    exact_mod_cast capacity_prefix_sum_le m k hgrowth j hj
  linarith

theorem strictMonoOn_capacities (m : ℕ → ℕ) (k : ℕ)
    (hpos : ∀ j, j < k → 1 ≤ m j)
    (hgrowth : ∀ j, j + 1 < k → 16 * m j ≤ m (j + 1)) :
    StrictMonoOn m (Set.Iio k) := by
  intro i hi j hj hij
  change i < k at hi
  change j < k at hj
  have hmono : StrictMonoOn m (Set.Iic j) := by
    apply strictMonoOn_Iic_of_lt_succ
    intro a ha
    have hp := hpos a (by omega)
    have hg := hgrowth a (by omega)
    change m a < m (a + 1)
    omega
  exact hmono (show i ≤ j from hij.le) (show j ≤ j from Nat.le_refl j) hij

/-- Index monotonicity also holds before an initial zero-capacity segment is
removed. No positivity assumption is needed here. -/
theorem monotoneOn_capacities (m : ℕ → ℕ) (k : ℕ)
    (hgrowth : ∀ j, j + 1 < k → 16 * m j ≤ m (j + 1)) :
    MonotoneOn m (Set.Iio k) := by
  apply monotoneOn_of_le_succ Set.ordConnected_Iio
  intro j _ _ hj
  have hg := hgrowth j hj
  change m j ≤ m (j + 1)
  omega

/-- A finite sum of distinct positive geometric powers. -/
theorem sum_positive_geometric_le (s : Finset ℕ) {q : ℝ}
    (hq : 0 ≤ q) (hq1 : q < 1) (hpos : ∀ m ∈ s, 1 ≤ m) :
    (∑ m ∈ s, q ^ m) ≤ q / (1 - q) := by
  obtain ⟨N, hN⟩ := s.exists_nat_subset_range
  calc
    (∑ m ∈ s, q ^ m) ≤ ∑ m ∈ Finset.Ico 1 N, q ^ m := by
      apply sum_le_sum_of_subset_of_nonneg
      · intro m hm
        exact Finset.mem_Ico.mpr ⟨hpos m hm, mem_range.mp (hN hm)⟩
      · intro m _ _
        exact pow_nonneg hq _
    _ ≤ q / (1 - q) := by
      simpa only [pow_one] using geom_sum_Ico_le_of_lt_one (m := 1) (n := N) hq hq1

/-- Elementary finite product bound, applied below to the retention factors. -/
theorem one_sub_sum_le_prod_one_sub {ι : Type*} (s : Finset ι) (f : ι → ℝ)
    (h0 : ∀ i ∈ s, 0 ≤ f i) (h1 : ∀ i ∈ s, f i ≤ 1) :
    1 - (∑ i ∈ s, f i) ≤ ∏ i ∈ s, (1 - f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      have h0i := h0 i (mem_insert_self _ _)
      have h1i := h1 i (mem_insert_self _ _)
      have h0s : ∀ j ∈ s, 0 ≤ f j := fun j hj => h0 j (mem_insert_of_mem hj)
      have h1s : ∀ j ∈ s, f j ≤ 1 := fun j hj => h1 j (mem_insert_of_mem hj)
      have hp := mul_le_mul_of_nonneg_left (ih h0s h1s) (sub_nonneg.mpr h1i)
      have hs := sum_nonneg h0s
      rw [sum_insert hi, prod_insert hi]
      nlinarith [mul_nonneg h0i hs]

theorem exp_neg_one_le_two_fifths : Real.exp (-1) ≤ (2 / 5 : ℝ) := by
  have he : (5 / 2 : ℝ) ≤ Real.exp 1 := by
    have h := Real.quadratic_le_exp_of_nonneg (show (0 : ℝ) ≤ 1 by norm_num)
    norm_num at h
    exact h
  rw [Real.exp_neg]
  apply (inv_le_iff_one_le_mul₀ (Real.exp_pos 1)).mpr
  nlinarith

theorem sum_exp_neg_capacities_le_two_thirds (s : Finset ℕ)
    (hpos : ∀ m ∈ s, 1 ≤ m) :
    (∑ m ∈ s, Real.exp (-(m : ℝ))) ≤ (2 / 3 : ℝ) := by
  have hq0 := (Real.exp_pos (-1)).le
  have hq1 : Real.exp (-1) < 1 := lt_of_le_of_lt exp_neg_one_le_two_fifths (by norm_num)
  have heq (m : ℕ) : Real.exp (-(m : ℝ)) = Real.exp (-1) ^ m := by
    simpa only [mul_neg_one] using Real.exp_nat_mul (-1) m
  simp_rw [heq]
  apply (sum_positive_geometric_le s hq0 hq1 hpos).trans
  apply (div_le_iff₀ (sub_pos.mpr hq1)).mpr
  nlinarith [exp_neg_one_le_two_fifths]

theorem finite_retentionProduct_ge_one_third (s : Finset ℕ)
    (hpos : ∀ m ∈ s, 1 ≤ m) :
    (1 / 3 : ℝ) ≤ ∏ m ∈ s, (1 - Real.exp (-(m : ℝ))) := by
  have h0 (m : ℕ) (_ : m ∈ s) : 0 ≤ Real.exp (-(m : ℝ)) := (Real.exp_pos _).le
  have h1 (m : ℕ) (_ : m ∈ s) : Real.exp (-(m : ℝ)) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    exact neg_nonpos.mpr (Nat.cast_nonneg m)
  have hb := one_sub_sum_le_prod_one_sub s (fun m => Real.exp (-(m : ℝ))) h0 h1
  have hs := sum_exp_neg_capacities_le_two_thirds s hpos
  linarith

theorem finite_spreadInflation_lt_four (s : Finset ℕ)
    (hpos : ∀ m ∈ s, 1 ≤ m) :
    (∏ m ∈ s, (1 - Real.exp (-(m : ℝ)))⁻¹) < 4 := by
  have hp := finite_retentionProduct_ge_one_third s hpos
  have hp0 : 0 < ∏ m ∈ s, (1 - Real.exp (-(m : ℝ))) := lt_of_lt_of_le (by norm_num) hp
  rw [Finset.prod_inv_distrib]
  apply (inv_lt_iff_one_lt_mul₀ hp0).mpr
  nlinarith

theorem spreadInflation_lt_four {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (m : ι → ℕ) (hpos : ∀ i ∈ s, 1 ≤ m i)
    (hinj : Set.InjOn m (↑s : Set ι)) :
    (∏ i ∈ s, (1 - Real.exp (-(m i : ℝ)))⁻¹) < 4 := by
  have heq : (∏ i ∈ s, (1 - Real.exp (-(m i : ℝ)))⁻¹) =
      ∏ n ∈ s.image m, (1 - Real.exp (-(n : ℝ)))⁻¹ := by
    symm
    exact Finset.prod_image hinj
  rw [heq]
  apply finite_spreadInflation_lt_four
  intro n hn
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hn
  exact hpos i hi

def iteratedSpread (σ : ℝ) (l t : ℕ) : ℝ :=
  σ * ∏ u ∈ range t, (1 - Real.exp (-(reducedCapacity l u : ℝ)))⁻¹

@[simp] theorem iteratedSpread_zero (σ : ℝ) (l : ℕ) : iteratedSpread σ l 0 = σ := by
  simp [iteratedSpread]

theorem iteratedSpread_succ (σ : ℝ) (l t : ℕ) :
    iteratedSpread σ l (t + 1) =
      iteratedSpread σ l t / (1 - Real.exp (-(reducedCapacity l t : ℝ))) := by
  simp only [iteratedSpread, prod_range_succ, div_eq_mul_inv, mul_assoc]

theorem halving_spreadInflation_lt_four {l t : ℕ} (hpos : 0 < reducedCapacity l t) :
    (∏ u ∈ range t, (1 - Real.exp (-(reducedCapacity l u : ℝ)))⁻¹) < 4 := by
  apply spreadInflation_lt_four (range t) (reducedCapacity l)
  · intro u hu
    exact le_trans hpos (antitone_reducedCapacity l (le_of_lt (mem_range.mp hu)))
  · intro u hu v hv huv
    exact (strictAntiOn_reducedCapacity hpos).injOn
      (le_of_lt (mem_range.mp hu)) (le_of_lt (mem_range.mp hv)) huv

theorem iteratedSpread_pos {σ : ℝ} (hσ : 0 < σ) {l t : ℕ}
    (hpos : 0 < reducedCapacity l t) : 0 < iteratedSpread σ l t := by
  apply mul_pos hσ
  apply Finset.prod_pos
  intro u hu
  apply inv_pos.mpr
  apply sub_pos.mpr
  rw [Real.exp_lt_one_iff]
  have hp : 0 < reducedCapacity l u :=
    lt_of_lt_of_le hpos (antitone_reducedCapacity l (mem_range.mp hu).le)
  exact neg_neg_of_pos (by exact_mod_cast hp)

theorem iteratedSpread_le_four_mul {σ : ℝ} (hσ : 0 < σ) {l t : ℕ}
    (hpos : 0 < reducedCapacity l t) : iteratedSpread σ l t ≤ 4 * σ := by
  have h := mul_lt_mul_of_pos_left (halving_spreadInflation_lt_four hpos) hσ
  simpa only [iteratedSpread, mul_comm σ 4] using h.le

theorem exp_neg_seven_le_one_eighth : Real.exp (-7) ≤ (1 / 8 : ℝ) := by
  have he : (8 : ℝ) ≤ Real.exp 7 := by
    have h := Real.add_one_le_exp (7 : ℝ)
    norm_num at h
    exact h
  rw [Real.exp_neg]
  apply (inv_le_iff_one_le_mul₀ (Real.exp_pos 7)).mpr
  nlinarith

theorem sum_exp_neg_seven_capacities_lt_one_quarter (s : Finset ℕ)
    (hpos : ∀ m ∈ s, 1 ≤ m) :
    (∑ m ∈ s, Real.exp (-7 * (m : ℝ))) < (1 / 4 : ℝ) := by
  have hq0 := (Real.exp_pos (-7)).le
  have hq1 : Real.exp (-7) < 1 := lt_of_le_of_lt exp_neg_seven_le_one_eighth (by norm_num)
  have heq (m : ℕ) : Real.exp (-7 * (m : ℝ)) = Real.exp (-7) ^ m := by
    simpa only [mul_comm] using Real.exp_nat_mul (-7) m
  simp_rw [heq]
  have hsum := sum_positive_geometric_le s hq0 hq1 hpos
  have hfrac : Real.exp (-7) / (1 - Real.exp (-7)) ≤ (1 / 7 : ℝ) := by
    apply (div_le_iff₀ (sub_pos.mpr hq1)).mpr
    nlinarith [exp_neg_seven_le_one_eighth]
  exact lt_of_le_of_lt (hsum.trans hfrac) (by norm_num)

theorem capacity_failure_sum_lt_one_quarter (m : ℕ → ℕ) (k : ℕ)
    (hpos : ∀ j, j < k → 1 ≤ m j)
    (hgrowth : ∀ j, j + 1 < k → 16 * m j ≤ m (j + 1)) :
    (∑ j ∈ range k,
      Real.exp (12 * (∑ h ∈ range j, (m h : ℝ)) - 8 * (m j : ℝ))) < (1 / 4 : ℝ) := by
  have hmono := strictMonoOn_capacities m k hpos hgrowth
  have hinj : Set.InjOn m (↑(range k) : Set ℕ) := by
    intro i hi j hj hij
    exact hmono.injOn (mem_range.mp hi) (mem_range.mp hj) hij
  calc
    (∑ j ∈ range k,
        Real.exp (12 * (∑ h ∈ range j, (m h : ℝ)) - 8 * (m j : ℝ)))
        ≤ ∑ j ∈ range k, Real.exp (-7 * (m j : ℝ)) := by
      apply Finset.sum_le_sum
      intro j hj
      apply Real.exp_le_exp.mpr
      have hs := capacity_prefix_sum_real_le m k hgrowth (mem_range.mp hj)
      have hm : 0 ≤ (m j : ℝ) := Nat.cast_nonneg _
      nlinarith
    _ = ∑ n ∈ (range k).image m, Real.exp (-7 * (n : ℝ)) := by
      symm
      exact Finset.sum_image hinj
    _ < 1 / 4 := by
      apply sum_exp_neg_seven_capacities_lt_one_quarter
      intro n hn
      obtain ⟨j, hj, rfl⟩ := mem_image.mp hn
      exact hpos j (mem_range.mp hj)

/-- A history-free allowance for the spread parameter at capacity `m`. -/
def capacityReserve (σ : ℝ) (m : ℕ) : ℝ :=
  4 * σ * ∏ j ∈ Finset.Icc 1 m, (1 - Real.exp (-(j : ℝ)))

theorem retentionFactor_pos {m : ℕ} (hm : 0 < m) :
    0 < 1 - Real.exp (-(m : ℝ)) := by
  apply sub_pos.mpr
  rw [Real.exp_lt_one_iff]
  exact neg_neg_of_pos (by exact_mod_cast hm)

theorem retentionFactor_le_one (m : ℕ) :
    1 - Real.exp (-(m : ℝ)) ≤ 1 := sub_le_self _ (Real.exp_pos _).le

@[simp] theorem capacityReserve_zero (σ : ℝ) : capacityReserve σ 0 = 4 * σ := by
  simp [capacityReserve]

theorem capacityReserve_pos {σ : ℝ} (hσ : 0 < σ) (m : ℕ) :
    0 < capacityReserve σ m := by
  apply mul_pos (mul_pos (by norm_num) hσ)
  apply Finset.prod_pos
  intro j hj
  exact retentionFactor_pos (Finset.mem_Icc.mp hj).1

theorem capacityReserve_lower {σ : ℝ} (hσ : 0 ≤ σ) (m : ℕ) :
    σ ≤ capacityReserve σ m := by
  have hp := finite_retentionProduct_ge_one_third (Finset.Icc 1 m)
    (fun j hj => (Finset.mem_Icc.mp hj).1)
  have hm := mul_le_mul_of_nonneg_left hp (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) hσ)
  unfold capacityReserve
  nlinarith

theorem capacityReserve_upper {σ : ℝ} (hσ : 0 ≤ σ) (m : ℕ) :
    capacityReserve σ m ≤ 4 * σ := by
  have hp : (∏ j ∈ Finset.Icc 1 m, (1 - Real.exp (-(j : ℝ)))) ≤ 1 := by
    apply Finset.prod_le_one₀
    · intro j hj
      exact (retentionFactor_pos (Finset.mem_Icc.mp hj).1).le
    · intro j _
      exact retentionFactor_le_one j
  have hm := mul_le_mul_of_nonneg_left hp (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) hσ)
  simpa only [capacityReserve, mul_one] using hm

theorem antitone_capacityReserve {σ : ℝ} (hσ : 0 ≤ σ) :
    Antitone (capacityReserve σ) := by
  intro a b hab
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) hσ)
  apply Finset.prod_le_prod_of_subset_of_le_one₀
  · intro j hj
    obtain ⟨hj1, hja⟩ := Finset.mem_Icc.mp hj
    exact Finset.mem_Icc.mpr ⟨hj1, hja.trans hab⟩
  · intro j hj
    exact (retentionFactor_pos (Finset.mem_Icc.mp hj).1).le
  · intro j _ _
    exact retentionFactor_le_one j

theorem capacityReserve_succ (σ : ℝ) (m : ℕ) :
    capacityReserve σ (m + 1) = capacityReserve σ m *
      (1 - Real.exp (-((m + 1 : ℕ) : ℝ))) := by
  simp only [capacityReserve, Finset.prod_Icc_succ_top (show 1 ≤ m + 1 by omega), mul_assoc]

theorem capacityReserve_div_le_half {σ : ℝ} (hσ : 0 ≤ σ) {m : ℕ} (hm : 0 < m) :
    capacityReserve σ m / (1 - Real.exp (-(m : ℝ))) ≤ capacityReserve σ (m / 2) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hm)
  rw [capacityReserve_succ, mul_div_cancel_right₀ _ (retentionFactor_pos (Nat.succ_pos m)).ne']
  exact antitone_capacityReserve hσ (show (m + 1) / 2 ≤ m by omega)

end LeanBlast.SecondKahnKalai

end

end OAI
