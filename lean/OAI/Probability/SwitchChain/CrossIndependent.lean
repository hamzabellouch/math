import OAI.Probability.SwitchChain.CrossMatrix
import OAI.Probability.SwitchChain.CrossCovariance

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem315.CrossBlock

def independentMargin (s : ℕ) (r : Fin 3) : ℝ :=
  match s with
  | 0 => if r = 0 then 1 else 0
  | 1 => if r ≤ 1 then 1 else 0
  | 3 => if 1 ≤ r then 1 else 0
  | 4 => if r = 2 then 1 else 0
  | _ => 0

theorem count_eq_independent_product (s : ℕ) (hs : s ≠ 2) (r c : Fin 3) :
    (count s r c : ℝ) = independentMargin s r * independentMargin s c := by
  by_cases hsmall : s ≤ 4
  · interval_cases s
    · rw [count_zero]
      simp only [independentMargin]
      split_ifs <;> simp_all
    · rw [count_one]
      simp only [independentMargin]
      split_ifs <;> simp_all
    · exact (hs rfl).elim
    · rw [count_three]
      simp only [independentMargin]
      split_ifs <;> simp_all
    · rw [count_four]
      simp only [independentMargin]
      split_ifs <;> simp_all
  · have hcount : count s r c = 0 := by
      unfold count
      apply Finset.card_eq_zero.mpr
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro M hM
      have ht := (Finset.mem_filter.mp hM).2.1
      have hb := total_le_four M
      omega
    have hmargin (t : Fin 3) : independentMargin s t = 0 := by
      match s with
      | 0 | 1 | 2 | 3 | 4 => omega
      | k + 5 => rfl
    rw [hcount, hmargin, hmargin]
    norm_num

variable {α β : Type*} [Fintype α] [Fintype β]

def countMoment (s : ℕ) (a : α → ℝ) (b : β → ℝ)
    (r : α → Fin 3) (c : β → Fin 3) (f : α → ℝ) (g : β → ℝ) : ℝ :=
  ∑ x, ∑ y, a x * b y * (count s (r x) (c y) : ℝ) * f x * g y

def countAverage (s : ℕ) (a : α → ℝ) (b : β → ℝ)
    (r : α → Fin 3) (c : β → Fin 3) (f : α → ℝ) (g : β → ℝ) : ℝ :=
  countMoment s a b r c f g / countMoment s a b r c (fun _ => 1) (fun _ => 1)

theorem countMoment_factor (s : ℕ) (hs : s ≠ 2) (a : α → ℝ) (b : β → ℝ)
    (r : α → Fin 3) (c : β → Fin 3) (f : α → ℝ) (g : β → ℝ) :
    countMoment s a b r c f g =
      (∑ x, a x * independentMargin s (r x) * f x) *
        (∑ y, b y * independentMargin s (c y) * g y) := by
  unfold countMoment
  simp_rw [count_eq_independent_product s hs]
  calc
    _ = ∑ x, ∑ y, (a x * independentMargin s (r x) * f x) *
        (b y * independentMargin s (c y) * g y) := by
      apply Finset.sum_congr rfl
      intro x _
      apply Finset.sum_congr rfl
      intro y _
      ring
    _ = _ := by simp only [← Finset.mul_sum, ← Finset.sum_mul]

theorem countAverage_independent (s : ℕ) (hs : s ≠ 2)
    (a : α → ℝ) (b : β → ℝ) (r : α → Fin 3) (c : β → Fin 3)
    (f : α → ℝ) (g : β → ℝ) :
    countAverage s a b r c f g =
      countAverage s a b r c f (fun _ => 1) *
        countAverage s a b r c (fun _ => 1) g := by
  unfold countAverage
  simp only [countMoment_factor s hs, mul_one]
  by_cases h : (∑ x, a x * independentMargin s (r x)) *
      (∑ y, b y * independentMargin s (c y)) = 0
  · simp [h]
  · field_simp

end Problem315.CrossBlock

namespace Problem315.CrossCovariance

variable {α β : Type*} [Fintype α] [Fintype β]

theorem independent_of_left_flag_constant
    (a : α → ℝ) (b : β → ℝ) (p : α → ℝ) (q : β → ℝ)
    (k : ℝ) (hk : ∀ x, a x ≠ 0 → p x = k)
    (f : α → ℝ) (g : β → ℝ) :
    jointAverage a b p q f g = jointAverage a b p q f (fun _ => 1) *
      jointAverage a b p q (fun _ => 1) g := by
  have hpf : (∑ x, a x * p x * f x) = k * ∑ x, a x * f x := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    by_cases hx : a x = 0
    · simp [hx]
    · rw [hk x hx]
      ring
  have hp : (∑ x, a x * p x) = k * ∑ x, a x := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    by_cases hx : a x = 0
    · simp [hx]
    · rw [hk x hx]
      ring
  have h := covariance_rank_one a b p q f g
  rw [hpf, hp] at h
  have hz : (∑ x, a x) * (k * ∑ x, a x * f x) -
      (k * ∑ x, a x) * (∑ x, a x * f x) = 0 := by ring
  rw [hz] at h
  simpa only [neg_zero, zero_mul, zero_div, sub_eq_zero] using h

theorem independent_of_right_flag_constant
    (a : α → ℝ) (b : β → ℝ) (p : α → ℝ) (q : β → ℝ)
    (k : ℝ) (hk : ∀ y, b y ≠ 0 → q y = k)
    (f : α → ℝ) (g : β → ℝ) :
    jointAverage a b p q f g = jointAverage a b p q f (fun _ => 1) *
      jointAverage a b p q (fun _ => 1) g := by
  have hqg : (∑ y, b y * q y * g y) = k * ∑ y, b y * g y := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro y _
    by_cases hy : b y = 0
    · simp [hy]
    · rw [hk y hy]
      ring
  have hq : (∑ y, b y * q y) = k * ∑ y, b y := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro y _
    by_cases hy : b y = 0
    · simp [hy]
    · rw [hk y hy]
      ring
  have h := covariance_rank_one a b p q f g
  rw [hqg, hq] at h
  have hz : (∑ y, b y) * (k * ∑ y, b y * g y) -
      (k * ∑ y, b y) * (∑ y, b y * g y) = 0 := by ring
  rw [hz] at h
  simpa only [mul_zero, zero_div, sub_eq_zero] using h

theorem independent_of_left_event_zero
    (a : α → ℝ) (b : β → ℝ) (p : α → ℝ) (q : β → ℝ)
    (ha : ∀ x, 0 ≤ a x) (hb : ∀ y, 0 ≤ b y)
    (hp : ∀ x, p x = 0 ∨ p x = 1) (hq : ∀ y, q y = 0 ∨ q y = 1)
    (hprob : jointAverage a b p q p (fun _ => 1) = 0)
    (f : α → ℝ) (g : β → ℝ) :
    jointAverage a b p q f g = jointAverage a b p q f (fun _ => 1) *
      jointAverage a b p q (fun _ => 1) g := by
  by_cases hmass : mass a b p q = 0
  · simp [jointAverage, hmass]
  have hm : jointMoment a b p q p (fun _ => 1) = 0 :=
    (div_eq_zero_iff.mp hprob).resolve_right hmass
  have hnn (x : α) (y : β) :
      0 ≤ a x * b y * (2 - p x - q y) * p x * 1 := by
    have hax := ha x
    have hby := hb y
    rcases hp x with hx | hx <;> rcases hq y with hy | hy <;>
      simp only [hx, hy] <;> positivity
  have hterm (x : α) (y : β) :
      a x * b y * (2 - p x - q y) * p x * 1 = 0 := by
    have hx := (Finset.sum_eq_zero_iff_of_nonneg
      (fun x _ => Finset.sum_nonneg (fun y _ => hnn x y))).mp hm x (Finset.mem_univ x)
    exact (Finset.sum_eq_zero_iff_of_nonneg (fun y _ => hnn x y)).mp hx y
      (Finset.mem_univ y)
  by_cases hconst : ∀ x, a x ≠ 0 → p x = 0
  · exact independent_of_left_flag_constant a b p q 0 hconst f g
  · push Not at hconst
    obtain ⟨x, hax, hpx⟩ := hconst
    have hp1 : p x = 1 := (hp x).resolve_left hpx
    apply independent_of_right_flag_constant a b p q 1 _ f g
    intro y hby
    rcases hq y with hy | hy
    · have hz := hterm x y
      simp only [hp1, hy] at hz
      norm_num at hz
      exact (hz.elim hax hby).elim
    · exact hy

theorem jointMoment_swap (a : α → ℝ) (b : β → ℝ) (p : α → ℝ) (q : β → ℝ)
    (f : α → ℝ) (g : β → ℝ) :
    jointMoment a b p q f g = jointMoment b a q p g f := by
  unfold jointMoment
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  apply Finset.sum_congr rfl
  intro x _
  ring

theorem jointAverage_swap (a : α → ℝ) (b : β → ℝ) (p : α → ℝ) (q : β → ℝ)
    (f : α → ℝ) (g : β → ℝ) :
    jointAverage a b p q f g = jointAverage b a q p g f := by
  unfold jointAverage mass
  rw [jointMoment_swap a b p q f g,
    jointMoment_swap a b p q (fun _ => 1) (fun _ => 1)]

theorem independent_of_right_event_zero
    (a : α → ℝ) (b : β → ℝ) (p : α → ℝ) (q : β → ℝ)
    (ha : ∀ x, 0 ≤ a x) (hb : ∀ y, 0 ≤ b y)
    (hp : ∀ x, p x = 0 ∨ p x = 1) (hq : ∀ y, q y = 0 ∨ q y = 1)
    (hprob : jointAverage a b p q (fun _ => 1) q = 0)
    (f : α → ℝ) (g : β → ℝ) :
    jointAverage a b p q f g = jointAverage a b p q f (fun _ => 1) *
      jointAverage a b p q (fun _ => 1) g := by
  rw [jointAverage_swap] at hprob
  have h := independent_of_left_event_zero b a q p hb ha hq hp hprob g f
  rw [jointAverage_swap b a q p g f,
    jointAverage_swap b a q p g (fun _ => 1),
    jointAverage_swap b a q p (fun _ => 1) f] at h
  simpa only [mul_comm] using h

theorem independent_of_center_zero
    (a : α → ℝ) (b : β → ℝ) (p : α → ℝ) (q : β → ℝ)
    (ha : ∀ x, 0 ≤ a x) (hb : ∀ y, 0 ≤ b y)
    (hp : ∀ x, p x = 0 ∨ p x = 1) (hq : ∀ y, q y = 0 ∨ q y = 1)
    (hprob : jointAverage a b p q (fun x => 1 - p x) (fun y => 1 - q y) = 0)
    (f : α → ℝ) (g : β → ℝ) :
    jointAverage a b p q f g = jointAverage a b p q f (fun _ => 1) *
      jointAverage a b p q (fun _ => 1) g := by
  by_cases hmass : mass a b p q = 0
  · simp [jointAverage, hmass]
  have hm : jointMoment a b p q (fun x => 1 - p x) (fun y => 1 - q y) = 0 :=
    (div_eq_zero_iff.mp hprob).resolve_right hmass
  have hnn (x : α) (y : β) :
      0 ≤ a x * b y * (2 - p x - q y) * (1 - p x) * (1 - q y) := by
    have hax := ha x
    have hby := hb y
    rcases hp x with hx | hx <;> rcases hq y with hy | hy <;>
      simp only [hx, hy] <;> positivity
  have hterm (x : α) (y : β) :
      a x * b y * (2 - p x - q y) * (1 - p x) * (1 - q y) = 0 := by
    have hx := (Finset.sum_eq_zero_iff_of_nonneg
      (fun x _ => Finset.sum_nonneg (fun y _ => hnn x y))).mp hm x (Finset.mem_univ x)
    exact (Finset.sum_eq_zero_iff_of_nonneg (fun y _ => hnn x y)).mp hx y
      (Finset.mem_univ y)
  by_cases hconst : ∀ x, a x ≠ 0 → p x = 1
  · exact independent_of_left_flag_constant a b p q 1 hconst f g
  · push Not at hconst
    obtain ⟨x, hax, hpx⟩ := hconst
    have hp0 : p x = 0 := (hp x).resolve_right hpx
    apply independent_of_right_flag_constant a b p q 1 _ f g
    intro y hby
    rcases hq y with hy | hy
    · have hz := hterm x y
      simp only [hp0, hy] at hz
      norm_num at hz
      exact (hz.elim hax hby).elim
    · exact hy

end Problem315.CrossCovariance

end

end OAI
