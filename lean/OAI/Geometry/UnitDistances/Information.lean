import OAI.Geometry.UnitDistances.Wedges

namespace OAI

namespace PlanarUnitDistances.FiniteInformation
open scoped InnerProductSpace
open Finset Real

noncomputable def KL {α : Type*} [Fintype α] (p q : α → ℝ) : ℝ :=
  ∑ a, p a * log (p a / q a)

noncomputable def TV {α : Type*} [Fintype α] (p q : α → ℝ) : ℝ :=
  (∑ a, |p a - q a|) / 2

lemma hellinger_pointwise {p q : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q)
    (hac : p ≠ 0 → q ≠ 0) :
    (sqrt p - sqrt q)^2 ≤ p * log (p/q) - p + q := by
  by_cases hpz : p = 0
  · simp [hpz, sq_sqrt hq]
  have hpp : 0 < p := lt_of_le_of_ne hp (Ne.symm hpz)
  have hqp : 0 < q := lt_of_le_of_ne hq (Ne.symm (hac hpz))
  have hspp := sqrt_pos.mpr hpp
  have hsqp := sqrt_pos.mpr hqp
  have hsp := sq_sqrt hp
  have hsq := sq_sqrt hq
  have hl := log_le_sub_one_of_pos (div_pos hsqp hspp)
  rw [log_div (ne_of_gt hsqp) (ne_of_gt hspp), log_sqrt hq, log_sqrt hp] at hl
  have hm : p * (sqrt q / sqrt p) = sqrt p * sqrt q := by
    rw [← mul_div_assoc]
    apply (div_eq_iff (ne_of_gt hspp)).mpr
    nlinarith
  have hh := mul_le_mul_of_nonneg_left hl (show 0 ≤ 2*p by positivity)
  rw [log_div hpz (hac hpz)]
  nlinarith

theorem hellinger_le_KL {α : Type*} [Fintype α] (p q : α → ℝ)
    (hp : ∀ a, 0 ≤ p a) (hq : ∀ a, 0 ≤ q a)
    (hpsum : ∑ a, p a = 1) (hqsum : ∑ a, q a = 1)
    (hac : ∀ a, p a ≠ 0 → q a ≠ 0) :
    (∑ a, (sqrt (p a) - sqrt (q a))^2) ≤ KL p q := by
  have hh := sum_le_sum (s := univ) (fun a _ => hellinger_pointwise (hp a) (hq a) (hac a))
  simpa only [sum_add_distrib, sum_sub_distrib, hpsum, hqsum, sub_add_cancel, KL] using hh

theorem TV_sq_le_KL {α : Type*} [Fintype α] (p q : α → ℝ)
    (hp : ∀ a, 0 ≤ p a) (hq : ∀ a, 0 ≤ q a)
    (hpsum : ∑ a, p a = 1) (hqsum : ∑ a, q a = 1)
    (hac : ∀ a, p a ≠ 0 → q a ≠ 0) : (TV p q)^2 ≤ KL p q := by
  have hH := hellinger_le_KL p q hp hq hpsum hqsum hac
  have hs : (∑ a, (sqrt (p a) + sqrt (q a))^2) ≤ 4 := by
    calc
      _ ≤ ∑ a, (2*p a + 2*q a) := by
        apply sum_le_sum
        intro a _
        nlinarith [sq_nonneg (sqrt (p a) - sqrt (q a)), sq_sqrt (hp a), sq_sqrt (hq a)]
      _ = 4 := by rw [sum_add_distrib, ← mul_sum, ← mul_sum, hpsum, hqsum]; norm_num
  have hid (a : α) : |p a-q a| =
      |sqrt (p a)-sqrt (q a)| * (sqrt (p a)+sqrt (q a)) := by
    rw [← abs_of_nonneg (show 0 ≤ sqrt (p a)+sqrt (q a) by positivity), ← abs_mul]
    congr 1
    nlinarith [sq_sqrt (hp a), sq_sqrt (hq a)]
  have hcs := sum_mul_sq_le_sq_mul_sq univ
    (fun a => |sqrt (p a)-sqrt (q a)|) (fun a => sqrt (p a)+sqrt (q a))
  simp only [← hid, sq_abs] at hcs
  have hm := mul_le_mul_of_nonneg_left hs
    (show 0 ≤ ∑ a, (sqrt (p a)-sqrt (q a))^2 by positivity)
  unfold TV
  nlinarith

theorem KL_nonneg {α : Type*} [Fintype α] (p q : α → ℝ)
    (hp : ∀ a, 0 ≤ p a) (hq : ∀ a, 0 ≤ q a)
    (hpsum : ∑ a, p a = 1) (hqsum : ∑ a, q a = 1)
    (hac : ∀ a, p a ≠ 0 → q a ≠ 0) : 0 ≤ KL p q :=
  (sq_nonneg _).trans (TV_sq_le_KL p q hp hq hpsum hqsum hac)

lemma KL_term_chain {p q P Q : ℝ} (hP : P ≠ 0) (hQ : Q ≠ 0)
    (hac : p ≠ 0 → q ≠ 0) :
    p * log (p/q) = p * log (P/Q) +
      P * ((p/P) * log ((p/P)/(q/Q))) := by
  by_cases hp : p = 0
  · simp [hp]
  have hq := hac hp
  rw [log_div (div_ne_zero hp hP) (div_ne_zero hq hQ),
    log_div hp hP, log_div hq hQ, log_div hp hq, log_div hP hQ]
  field_simp
  ring

lemma sum_ac {α : Type*} [Fintype α] {p q : α → ℝ}
    (hq : ∀ a, 0 ≤ q a) (hac : ∀ a, p a ≠ 0 → q a ≠ 0)
    (hp : ∑ a, p a ≠ 0) : ∑ a, q a ≠ 0 := by
  intro hqz
  have hz := (sum_eq_zero_iff_of_nonneg (fun a _ => hq a)).mp hqz
  apply hp
  apply sum_eq_zero
  intro a ha
  by_contra hh
  exact hac a hh (hz a ha)

theorem KL_chain {α β : Type*} [Fintype α] [Fintype β]
    (p q : α × β → ℝ) (hp : ∀ ab, 0 ≤ p ab) (hq : ∀ ab, 0 ≤ q ab)
    (hac : ∀ ab, p ab ≠ 0 → q ab ≠ 0) :
    KL p q = KL (fun a => ∑ b, p (a,b)) (fun a => ∑ b, q (a,b)) +
      ∑ a, (∑ b, p (a,b)) *
        KL (fun b => p (a,b) / (∑ c, p (a,c)))
          (fun b => q (a,b) / (∑ c, q (a,c))) := by
  unfold KL
  rw [Fintype.sum_prod_type, ← sum_add_distrib]
  apply sum_congr rfl
  intro a _
  by_cases hz : ∑ b, p (a,b) = 0
  · have hpz := (sum_eq_zero_iff_of_nonneg (fun b _ => hp (a,b))).mp hz
    simp [fun b => hpz b (mem_univ b)]
  have hqz := sum_ac (fun b => hq (a,b)) (fun b => hac (a,b)) hz
  calc
    _ = ∑ b, (p (a,b) * log ((∑ c, p (a,c)) / (∑ c, q (a,c))) +
          (∑ c, p (a,c)) * ((p (a,b) / (∑ c, p (a,c))) *
            log ((p (a,b) / (∑ c, p (a,c))) / (q (a,b) / (∑ c, q (a,c)))))) := by
      apply sum_congr rfl
      intro b _
      exact KL_term_chain hz hqz (hac (a,b))
    _ = _ := by rw [sum_add_distrib, sum_mul, mul_sum]

theorem KL_fst_le {α β : Type*} [Fintype α] [Fintype β]
    (p q : α × β → ℝ) (hp : ∀ ab, 0 ≤ p ab) (hq : ∀ ab, 0 ≤ q ab)
    (hac : ∀ ab, p ab ≠ 0 → q ab ≠ 0) :
    KL (fun a => ∑ b, p (a,b)) (fun a => ∑ b, q (a,b)) ≤ KL p q := by
  rw [KL_chain p q hp hq hac]
  apply le_add_of_nonneg_right
  apply sum_nonneg
  intro a _
  by_cases hz : ∑ b, p (a,b) = 0
  · simp [hz]
  have hP : 0 ≤ ∑ b, p (a,b) := sum_nonneg fun b _ => hp (a,b)
  have hQ : 0 ≤ ∑ b, q (a,b) := sum_nonneg fun b _ => hq (a,b)
  have hqz := sum_ac (fun b => hq (a,b)) (fun b => hac (a,b)) hz
  apply mul_nonneg hP
  apply KL_nonneg
  · intro b; exact div_nonneg (hp (a,b)) hP
  · intro b; exact div_nonneg (hq (a,b)) hQ
  · rw [← sum_div, div_self hz]
  · rw [← sum_div, div_self hqz]
  · intro b hb
    apply div_ne_zero
    · apply hac (a,b)
      intro hh
      exact hb (by simp [hh])
    · exact hqz

noncomputable def push {α β : Type*} [Fintype α] [DecidableEq β]
    (p : α → ℝ) (f : α → β) (b : β) : ℝ :=
  ∑ a, if f a = b then p a else 0

lemma push_nonneg {α β : Type*} [Fintype α] [DecidableEq β]
    {p : α → ℝ} (hp : ∀ a, 0 ≤ p a) (f : α → β) (b : β) :
    0 ≤ push p f b := by
  apply sum_nonneg
  intro a _
  split_ifs
  · exact hp a
  · exact le_rfl

lemma push_sum {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    (p : α → ℝ) (f : α → β) : ∑ b, push p f b = ∑ a, p a := by
  unfold push
  rw [sum_comm]
  simp

lemma push_ac {α β : Type*} [Fintype α] [DecidableEq β]
    {p q : α → ℝ} (hq : ∀ a, 0 ≤ q a)
    (hac : ∀ a, p a ≠ 0 → q a ≠ 0) (f : α → β) (b : β) :
    push p f b ≠ 0 → push q f b ≠ 0 := by
  apply sum_ac
  · intro a; split_ifs; exact hq a; exact le_rfl
  · intro a ha; split_ifs at * <;> simp_all

lemma KL_graph {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    (p q : α → ℝ) (f : α → β) :
    KL (fun ba : β × α => if f ba.2 = ba.1 then p ba.2 else 0)
      (fun ba : β × α => if f ba.2 = ba.1 then q ba.2 else 0) = KL p q := by
  unfold KL
  rw [Fintype.sum_prod_type, sum_comm]
  apply sum_congr rfl
  intro a _
  simp only
  conv_lhs => arg 2; ext b; rw [apply_ite₂ (fun x y : ℝ => x * log (x/y))]
  simp

theorem KL_push_le {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    (p q : α → ℝ) (hp : ∀ a, 0 ≤ p a) (hq : ∀ a, 0 ≤ q a)
    (hac : ∀ a, p a ≠ 0 → q a ≠ 0) (f : α → β) :
    KL (push p f) (push q f) ≤ KL p q := by
  rw [← KL_graph p q f]
  apply KL_fst_le (fun ba : β × α => if f ba.2 = ba.1 then p ba.2 else 0)
    (fun ba : β × α => if f ba.2 = ba.1 then q ba.2 else 0)
  · intro ba; split_ifs; exact hp ba.2; exact le_rfl
  · intro ba; split_ifs; exact hq ba.2; exact le_rfl
  · intro ba ha; split_ifs at * <;> simp_all

theorem KL_push_chain {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    (p q : α → ℝ) (hp : ∀ a, 0 ≤ p a) (hq : ∀ a, 0 ≤ q a)
    (hac : ∀ a, p a ≠ 0 → q a ≠ 0) (f : α → β) :
    KL p q = KL (push p f) (push q f) +
      ∑ b, push p f b * KL
        (fun a => (if f a = b then p a else 0) / push p f b)
        (fun a => (if f a = b then q a else 0) / push q f b) := by
  rw [← KL_graph p q f]
  apply KL_chain
  · intro ba; split_ifs; exact hp ba.2; exact le_rfl
  · intro ba; split_ifs; exact hq ba.2; exact le_rfl
  · intro ba ha; split_ifs at * <;> simp_all

theorem expectation_TV {α : Type*} [Fintype α] (p q F : α → ℝ)
    {B : ℝ} (hF : ∀ a, |F a| ≤ B) :
    |(∑ a, p a * F a) - ∑ a, q a * F a| ≤ 2 * B * TV p q := by
  unfold TV
  calc
    _ = |∑ a, (p a-q a)*F a| := by rw [← sum_sub_distrib]; congr 1; apply sum_congr rfl; intros; ring
    _ ≤ ∑ a, |(p a-q a)*F a| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ a, |p a-q a| * B := by
      apply sum_le_sum; intro a _; rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hF a) (abs_nonneg _)
    _ = _ := by rw [← sum_mul]; ring

noncomputable def row {α β : Type*} [Fintype β] (p : α × β → ℝ) (a : α) : ℝ :=
  ∑ b, p (a,b)

noncomputable def cond {α β : Type*} [Fintype β] (p : α × β → ℝ)
    (a : α) (b : β) : ℝ := p (a,b) / row p a

lemma row_nonneg {α β : Type*} [Fintype β] {p : α × β → ℝ}
    (hp : ∀ ab, 0 ≤ p ab) (a : α) : 0 ≤ row p a := sum_nonneg fun b _ => hp (a,b)

lemma row_ac {α β : Type*} [Fintype β] {p q : α × β → ℝ}
    (hq : ∀ ab, 0 ≤ q ab) (hac : ∀ ab, p ab ≠ 0 → q ab ≠ 0)
    (a : α) : row p a ≠ 0 → row q a ≠ 0 :=
  sum_ac (fun b => hq (a,b)) (fun b => hac (a,b))

lemma cond_nonneg {α β : Type*} [Fintype β] {p : α × β → ℝ}
    (hp : ∀ ab, 0 ≤ p ab) (a : α) (b : β) : 0 ≤ cond p a b :=
  div_nonneg (hp (a,b)) (row_nonneg hp a)

lemma cond_sum {α β : Type*} [Fintype β] (p : α × β → ℝ) (a : α)
    (ha : row p a ≠ 0) : ∑ b, cond p a b = 1 := by
  simp only [cond, ← sum_div]
  exact div_self ha

lemma cond_ac {α β : Type*} [Fintype β] {p q : α × β → ℝ}
    (hq : ∀ ab, 0 ≤ q ab) (hac : ∀ ab, p ab ≠ 0 → q ab ≠ 0)
    (a : α) (ha : row p a ≠ 0) (b : β) :
    cond p a b ≠ 0 → cond q a b ≠ 0 := by
  intro hb
  apply div_ne_zero
  · apply hac (a,b)
    intro hz
    exact hb (by simp [cond, hz])
  · exact row_ac hq hac a ha

lemma cond_KL_nonneg {α β : Type*} [Fintype β] {p q : α × β → ℝ}
    (hp : ∀ ab, 0 ≤ p ab) (hq : ∀ ab, 0 ≤ q ab)
    (hac : ∀ ab, p ab ≠ 0 → q ab ≠ 0) (a : α) (ha : row p a ≠ 0) :
    0 ≤ KL (cond p a) (cond q a) :=
  KL_nonneg _ _ (cond_nonneg hp a) (cond_nonneg hq a)
    (cond_sum p a ha) (cond_sum q a (row_ac hq hac a ha)) (cond_ac hq hac a ha)

theorem conditional_TV_sq {α β : Type*} [Fintype α] [Fintype β]
    (p q : α × β → ℝ) (hp : ∀ ab, 0 ≤ p ab) (hq : ∀ ab, 0 ≤ q ab)
    (hpsum : ∑ ab, p ab = 1) (hac : ∀ ab, p ab ≠ 0 → q ab ≠ 0) :
    (∑ a, row p a * TV (cond p a) (cond q a))^2 ≤ KL p q - KL (row p) (row q) := by
  have hcs := sum_sq_le_sum_mul_sum_of_sq_le_mul (R := ℝ) univ
    (r := fun a => row p a * TV (cond p a) (cond q a))
    (f := row p) (g := fun a => row p a * KL (cond p a) (cond q a))
    (fun a _ => row_nonneg hp a)
    (fun a _ => by
      by_cases ha : row p a = 0
      · simp [ha]
      · exact mul_nonneg (row_nonneg hp a) (cond_KL_nonneg hp hq hac a ha))
    (fun a _ => by
      by_cases ha : row p a = 0
      · simp [ha]
      have hh := TV_sq_le_KL (cond p a) (cond q a)
        (cond_nonneg hp a) (cond_nonneg hq a)
        (cond_sum p a ha) (cond_sum q a (row_ac hq hac a ha)) (cond_ac hq hac a ha)
      nlinarith [mul_le_mul_of_nonneg_left hh (sq_nonneg (row p a))])
  have hs : ∑ a, row p a = 1 := by
    simpa only [row, ← Fintype.sum_prod_type] using hpsum
  rw [hs, one_mul] at hcs
  have hc := KL_chain p q hp hq hac
  change KL p q = KL (row p) (row q) + ∑ a, row p a * KL (cond p a) (cond q a) at hc
  linarith

lemma row_expectation {α β : Type*} [Fintype β] (p : α × β → ℝ)
    (hp : ∀ ab, 0 ≤ p ab) (F : α × β → ℝ) (a : α) :
    (∑ b, p (a,b) * F (a,b)) = row p a * ∑ b, cond p a b * F (a,b) := by
  by_cases ha : row p a = 0
  · have hz := (sum_eq_zero_iff_of_nonneg (fun b _ => hp (a,b))).mp ha
    simp [ha, fun b => hz b (mem_univ b)]
  rw [mul_sum]
  apply sum_congr rfl
  intro b _
  dsimp [cond]
  field_simp

theorem conditional_centered_bound {α β : Type*} [Fintype α] [Fintype β]
    (p q : α × β → ℝ) (hp : ∀ ab, 0 ≤ p ab) (hq : ∀ ab, 0 ≤ q ab)
    (hpsum : ∑ ab, p ab = 1) (hac : ∀ ab, p ab ≠ 0 → q ab ≠ 0)
    (F : α × β → ℝ) {B : ℝ} (hB : 0 ≤ B) (hF : ∀ ab, |F ab| ≤ B)
    (hc : ∀ a, row p a ≠ 0 → ∑ b, cond q a b * F (a,b) = 0) :
    |∑ ab, p ab * F ab| ≤ 2*B*sqrt (KL p q - KL (row p) (row q)) := by
  have hv := conditional_TV_sq p q hp hq hpsum hac
  have hvs : (∑ a, row p a * TV (cond p a) (cond q a)) ≤
      sqrt (KL p q-KL (row p) (row q)) := le_sqrt_of_sq_le hv
  calc
    _ = |∑ a, ∑ b, p (a,b)*F (a,b)| := by rw [Fintype.sum_prod_type]
    _ ≤ ∑ a, |∑ b, p (a,b)*F (a,b)| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ a, 2*B*(row p a*TV (cond p a) (cond q a)) := by
      apply sum_le_sum
      intro a _
      rw [row_expectation p hp F a, abs_mul, abs_of_nonneg (row_nonneg hp a)]
      by_cases ha : row p a = 0
      · simp [ha]
      have hh := expectation_TV (cond p a) (cond q a) (fun b => F (a,b)) (fun b => hF (a,b))
      rw [hc a ha, sub_zero] at hh
      have hm := mul_le_mul_of_nonneg_left hh (row_nonneg hp a)
      nlinarith
    _ = 2*B*(∑ a, row p a*TV (cond p a) (cond q a)) := by rw [mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left hvs (by positivity)

lemma push_expectation {α β V : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    [AddCommMonoid V] [Module ℝ V] (p : α → ℝ) (f : α → β) (v : β → V) :
    ∑ b, push p f b • v b = ∑ a, p a • v (f a) := by
  unfold push
  simp only [sum_smul]
  rw [sum_comm]
  apply sum_congr rfl
  intro a _
  simp only [ite_smul, zero_smul]
  simp

lemma push_comp {α β γ : Type*} [Fintype α] [Fintype β]
    [DecidableEq β] [DecidableEq γ] (p : α → ℝ) (f : α → β) (g : β → γ) :
    push (push p f) g = push p (g ∘ f) := by
  classical
  funext c
  unfold push
  simp_rw [show ∀ b, (if g b = c then ∑ a, if f a = b then p a else 0 else 0) =
      ∑ a, if g b = c then (if f a = b then p a else 0) else 0 from
    fun b => by split_ifs <;> simp]
  rw [sum_comm]
  apply sum_congr rfl
  intro a _
  have hi : ∀ b, (if g b = c then if f a = b then p a else 0 else 0) =
      if f a = b then (if g b = c then p a else 0) else 0 := by
    intro b
    split_ifs <;> rfl
  simp_rw [hi]
  simp

lemma push_id {α : Type*} [Fintype α] [DecidableEq α] (p : α → ℝ) :
    push p id = p := by
  funext a
  simp [push]

lemma push_equiv {α β : Type*} [Fintype α] [DecidableEq β]
    (p : α → ℝ) (e : α ≃ β) (b : β) : push p e b = p (e.symm b) := by
  classical
  unfold push
  simp_rw [← e.eq_symm_apply]
  simp

lemma KL_push_equiv {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    (p q : α → ℝ) (e : α ≃ β) : KL (push p e) (push q e) = KL p q := by
  simp only [KL, push_equiv]
  exact Equiv.sum_comp e.symm (fun a => p a * log (p a / q a))

lemma push_pair {α β γ δ : Type*} [Fintype α] [Fintype β]
    [DecidableEq γ] [DecidableEq δ] (p : α → ℝ) (q : β → ℝ)
    (f : α → γ) (g : β → δ) (c : γ) (d : δ) :
    push (fun ab : α × β => p ab.1*q ab.2) (fun ab => (f ab.1,g ab.2)) (c,d) =
      push p f c * push q g d := by
  classical
  unfold push
  rw [Fintype.sum_prod_type, sum_mul_sum]
  apply sum_congr rfl
  intro a _
  apply sum_congr rfl
  intro b _
  simp only [Prod.mk.injEq]
  split_ifs <;> simp_all

lemma push_fst {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α]
    (p : α × β → ℝ) : push p Prod.fst = row p := by
  funext a
  unfold push row
  rw [Fintype.sum_prod_type, sum_comm]
  simp

lemma row_refinement {α β γ : Type*} [Fintype α] [Fintype γ]
    [DecidableEq β] [DecidableEq γ] (p : α → ℝ) (h : α → β) (c : α → γ) :
    row (push p (fun a => (h a,c a))) = push p h := by
  funext b
  unfold row push
  rw [sum_comm]
  apply sum_congr rfl
  intro a _
  simp only [Prod.mk.injEq]
  by_cases ha : h a = b <;> simp [ha]

lemma KL_refinement_nonneg {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
    [DecidableEq β] [DecidableEq γ] (p q : α → ℝ)
    (hp : ∀ a, 0 ≤ p a) (hq : ∀ a, 0 ≤ q a)
    (hac : ∀ a, p a ≠ 0 → q a ≠ 0) (h : α → β) (c : α → γ) :
    0 ≤ KL (push p (fun a => (h a,c a))) (push q (fun a => (h a,c a))) -
      KL (push p h) (push q h) := by
  rw [← row_refinement p h c, ← row_refinement q h c]
  apply sub_nonneg.mpr
  exact KL_fst_le _ _ (push_nonneg hp _) (push_nonneg hq _) (push_ac hq hac _)

section Features
variable {H C V : Type*} [Fintype H] [Fintype C]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]

noncomputable def mean (x : H × C → ℝ) (v : C → V) (h : H) : V :=
  ∑ c, cond x h c • v c

omit [Fintype H] in
lemma norm_mean_le (x : H × C → ℝ) (hx : ∀ hc, 0 ≤ x hc)
    (v : C → V) {B : ℝ} (hB : 0 ≤ B) (hv : ∀ c, ‖v c‖ ≤ B) (h : H) :
    ‖mean x v h‖ ≤ B := by
  by_cases hr : row x h = 0
  · simp [mean, cond, hr, hB]
  calc
    _ ≤ ∑ c, ‖cond x h c • v c‖ := norm_sum_le _ _
    _ = ∑ c, cond x h c * ‖v c‖ := by
      apply sum_congr rfl
      intro c _
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (cond_nonneg hx h c)]
    _ ≤ ∑ c, cond x h c * B := by
      apply sum_le_sum
      intro c _
      exact mul_le_mul_of_nonneg_left (hv c) (cond_nonneg hx h c)
    _ = B := by rw [← sum_mul, cond_sum x h hr, one_mul]

omit [Fintype H] in
lemma centered_mean (x : H × C → ℝ) (v : C → V) (h : H)
    (hr : row x h ≠ 0) :
    ∑ c, cond x h c • (v c - mean x v h) = 0 := by
  rw [show (fun c => cond x h c • (v c - mean x v h)) =
    (fun c => cond x h c • v c - cond x h c • mean x v h) by
      funext c; rw [smul_sub], sum_sub_distrib, ← sum_smul, cond_sum x h hr, one_smul]
  exact sub_self _

noncomputable def paired (x : H × C → ℝ) : (H × H) × (C × C) → ℝ :=
  fun a => x (a.1.1,a.2.1)*x (a.1.2,a.2.2)

omit [Fintype H] in
lemma paired_row (x : H × C → ℝ) (h : H × H) :
    row (paired x) h = row x h.1 * row x h.2 := by
  simp only [row, paired, Fintype.sum_prod_type, sum_mul_sum]

omit [Fintype H] in
lemma paired_cond (x : H × C → ℝ) (h : H × H) (c : C × C) :
    cond (paired x) h c = cond x h.1 c.1 * cond x h.2 c.2 := by
  simp only [cond, paired_row, paired, mul_div_mul_comm]

omit [Fintype H] in
lemma paired_centered (x : H × C → ℝ) (v : C → V) (h : H × H)
    (hr : row (paired x) h ≠ 0) :
    ∑ c, cond (paired x) h c *
      ⟪v c.1 - mean x v h.1, v c.2 - mean x v h.2⟫_ℝ = 0 := by
  rw [paired_row] at hr
  have h1 := (mul_ne_zero_iff.mp hr).1
  have h2 := (mul_ne_zero_iff.mp hr).2
  simp only [paired_cond, Fintype.sum_prod_type]
  calc
    _ = ⟪∑ c, cond x h.1 c • (v c - mean x v h.1),
        ∑ c, cond x h.2 c • (v c - mean x v h.2)⟫_ℝ := by
      simp only [sum_inner, inner_sum, real_inner_smul_left, real_inner_smul_right]
      conv_rhs => rw [sum_comm]
      apply sum_congr rfl
      intro c _
      apply sum_congr rfl
      intro d _
      ring
    _ = 0 := by rw [centered_mean x v h.1 h1, inner_zero_left]

theorem feature_increment (a : (H × H) × (C × C) → ℝ)
    (x : H × C → ℝ) (ha : ∀ v, 0 ≤ a v) (hx : ∀ v, 0 ≤ x v)
    (hs : ∑ v, a v = 1) (hac : ∀ v, a v ≠ 0 → paired x v ≠ 0)
    (v : C → V) {B : ℝ} (hB : 0 ≤ B) (hv : ∀ c, ‖v c‖ ≤ B) :
    |∑ hc, a hc * ⟪v hc.2.1 - mean x v hc.1.1,
      v hc.2.2 - mean x v hc.1.2⟫_ℝ| ≤
      8*B^2*sqrt (KL a (paired x) - KL (row a) (row (paired x))) := by
  have hn : ∀ h c, ‖v c - mean x v h‖ ≤ 2*B := by
    intro h c
    calc
      _ ≤ ‖v c‖ + ‖mean x v h‖ := norm_sub_le _ _
      _ ≤ B+B := add_le_add (hv c) (norm_mean_le x hx v hB hv h)
      _ = 2*B := by ring
  convert conditional_centered_bound a (paired x) ha
    (fun a => mul_nonneg (hx _) (hx _)) hs hac
    (fun hc => ⟪v hc.2.1 - mean x v hc.1.1, v hc.2.2 - mean x v hc.1.2⟫_ℝ)
    (B := 4*B^2) (by positivity) (fun hc => ?_) (fun h hh => ?_) using 1 <;> try ring_nf
  · calc
      _ ≤ ‖v hc.2.1-mean x v hc.1.1‖*‖v hc.2.2-mean x v hc.1.2‖ :=
        abs_real_inner_le_norm _ _
      _ ≤ (2*B)*(2*B) := mul_le_mul (hn _ _) (hn _ _) (norm_nonneg _) (by positivity)
      _ = _ := by ring
  · exact paired_centered x v h (row_ac (fun a => mul_nonneg (hx _) (hx _)) hac h hh)
end Features

section Observation
variable {P H C : Type*} [Fintype P] [Fintype H] [Fintype C]
  [DecidableEq H] [DecidableEq C]

def observation (h : P → H) (c : P → C) (pr : P × P) : (H × H) × (C × C) :=
  ((h pr.1,h pr.2),(c pr.1,c pr.2))

omit [Fintype H] [Fintype C] in
lemma product_observation (μ : P → ℝ) (h : P → H) (c : P → C) :
    push (fun pr : P × P => μ pr.1 * μ pr.2) (observation h c) =
      paired (push μ (fun p => (h p,c p))) := by
  funext a
  rcases a with ⟨⟨h1,h2⟩,⟨c1,c2⟩⟩
  dsimp [push, observation, paired]
  rw [Fintype.sum_prod_type, sum_mul_sum]
  apply sum_congr rfl
  intro p _
  apply sum_congr rfl
  intro r _
  simp only [Prod.mk.injEq]
  split_ifs <;> simp_all

omit [Fintype H] in
lemma observation_row (pLaw : P × P → ℝ) (h : P → H) (c : P → C) :
    row (push pLaw (observation h c)) = push pLaw (fun pr => (h pr.1,h pr.2)) :=
  row_refinement pLaw (fun pr => (h pr.1,h pr.2)) (fun pr => (c pr.1,c pr.2))

lemma observation_entropy (pLaw ρ : P × P → ℝ) (h : P → H) (c : P → C) :
    KL (push pLaw (observation h c)) (push ρ (observation h c)) =
      KL (push pLaw (fun pr => ((h pr.1,c pr.1),(h pr.2,c pr.2))))
        (push ρ (fun pr => ((h pr.1,c pr.1),(h pr.2,c pr.2)))) := by
  let e := Equiv.prodProdProdComm H H C C
  rw [← KL_push_equiv (push pLaw (observation h c)) (push ρ (observation h c)) e,
    push_comp, push_comp]
  rfl

theorem observation_covariance {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (pLaw : P × P → ℝ) (μ : P → ℝ) (hpLaw : ∀ pr, 0 ≤ pLaw pr) (hμ : ∀ p, 0 ≤ μ p)
    (hs : ∑ pr, pLaw pr = 1) (hac : ∀ pr, pLaw pr ≠ 0 → μ pr.1 * μ pr.2 ≠ 0)
    (h : P → H) (c : P → C) (v : C → V) {B : ℝ} (hB : 0 ≤ B)
    (hv : ∀ c, ‖v c‖ ≤ B) :
    |∑ pr, pLaw pr *
      ⟪v (c pr.1) - mean (push μ (fun p => (h p,c p))) v (h pr.1),
       v (c pr.2) - mean (push μ (fun p => (h p,c p))) v (h pr.2)⟫_ℝ| ≤
    8*B^2*sqrt (
      KL (push pLaw (fun pr => ((h pr.1,c pr.1),(h pr.2,c pr.2))))
        (push (fun pr : P × P => μ pr.1*μ pr.2)
          (fun pr => ((h pr.1,c pr.1),(h pr.2,c pr.2)))) -
      KL (push pLaw (fun pr => (h pr.1,h pr.2)))
        (push (fun pr : P × P => μ pr.1*μ pr.2) (fun pr => (h pr.1,h pr.2)))) := by
  let ρ : P × P → ℝ := fun pr => μ pr.1*μ pr.2
  have hr : ∀ pr, 0 ≤ ρ pr := fun pr => mul_nonneg (hμ _) (hμ _)
  have he := feature_increment (push pLaw (observation h c))
    (push μ (fun p => (h p,c p))) (push_nonneg hpLaw _) (push_nonneg hμ _)
    (by rw [push_sum]; exact hs)
    (by rw [← product_observation]; exact push_ac hr hac _) v hB hv
  rw [← product_observation μ h c, observation_entropy, observation_row,
    observation_row] at he
  have hf := push_expectation pLaw (observation h c)
    (fun hc : (H × H) × (C × C) =>
      ⟪v hc.2.1 - mean (push μ (fun p => (h p,c p))) v hc.1.1,
        v hc.2.2 - mean (push μ (fun p => (h p,c p))) v hc.1.2⟫_ℝ)
  simp only [smul_eq_mul, observation] at hf
  rwa [hf] at he
end Observation

section Wedges
variable {P Q V : Type*} [Fintype P] [Fintype Q]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]

noncomputable def wedge (κ : Q → ℝ) (w : Q → P → ℝ) (pr : P × P) : ℝ :=
  ∑ q, κ q * w q pr.1 * w q pr.2

theorem wedge_square (κ : Q → ℝ) (w : Q → P → ℝ) (U : P → V) :
    (∑ pr, wedge κ w pr * ⟪U pr.1,U pr.2⟫_ℝ) =
      ∑ q, κ q * ‖∑ p, w q p • U p‖^2 := by
  unfold wedge
  simp only [sum_mul]
  rw [sum_comm]
  apply sum_congr rfl
  intro q _
  rw [← real_inner_self_eq_norm_sq]
  simp only [sum_inner, inner_sum, real_inner_smul_left, real_inner_smul_right,
    Fintype.sum_prod_type, mul_sum]
  conv_rhs => rw [sum_comm]
  apply sum_congr rfl
  intro p _
  apply sum_congr rfl
  intro r _
  ring

omit [Fintype P] in
lemma wedge_nonneg (κ : Q → ℝ) (w : Q → P → ℝ)
    (hκ : ∀ q, 0 ≤ κ q) (hw : ∀ q p, 0 ≤ w q p) (pr : P × P) :
    0 ≤ wedge κ w pr := sum_nonneg fun q _ => mul_nonneg (mul_nonneg (hκ q) (hw q _)) (hw q _)

lemma wedge_sum (κ : Q → ℝ) (w : Q → P → ℝ)
    (hsκ : ∑ q, κ q = 1) (hsw : ∀ q, ∑ p, w q p = 1) :
    ∑ pr, wedge κ w pr = 1 := by
  unfold wedge
  rw [sum_comm]
  simp only [Fintype.sum_prod_type, ← mul_sum, hsw, mul_one]
  exact hsκ

theorem weighted_inner_bound (κ : Q → ℝ) (hκ : ∀ q, 0 ≤ κ q)
    (hsκ : ∑ q, κ q = 1) (a g : Q → V) {B : ℝ} (hB : 0 ≤ B)
    (hg : ∀ q, ‖g q‖ ≤ B) :
    |∑ q, κ q * ⟪a q,g q⟫_ℝ| ≤ B * sqrt (∑ q, κ q * ‖a q‖^2) := by
  have hc := sum_sq_le_sum_mul_sum_of_sq_le_mul (R := ℝ) univ
    (r := fun q => κ q * ‖a q‖) (f := κ) (g := fun q => κ q * ‖a q‖^2)
    (fun q _ => hκ q) (fun q _ => mul_nonneg (hκ q) (sq_nonneg _))
    (fun q _ => by ring_nf; exact le_rfl)
  rw [hsκ, one_mul] at hc
  have hsr := le_sqrt_of_sq_le hc
  calc
    _ ≤ ∑ q, |κ q * ⟪a q,g q⟫_ℝ| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ q, κ q * (‖a q‖ * B) := by
      apply sum_le_sum
      intro q _
      rw [abs_mul, abs_of_nonneg (hκ q)]
      apply mul_le_mul_of_nonneg_left _ (hκ q)
      exact (abs_real_inner_le_norm _ _).trans
        (mul_le_mul_of_nonneg_left (hg q) (norm_nonneg _))
    _ = B * ∑ q, κ q * ‖a q‖ := by rw [mul_sum]; apply sum_congr rfl; intros; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hsr hB
end Wedges

universe u
def History (C : Type u) : ℕ → Type u
  | 0 => PUnit
  | n+1 => History C n × C

instance historyFintype (C : Type*) [Fintype C] : (n : ℕ) → Fintype (History C n)
  | 0 => inferInstanceAs (Fintype PUnit)
  | n+1 => by
      letI : Fintype (History C n) := historyFintype C n
      exact inferInstanceAs (Fintype (History C n × C))

instance historyDecidableEq (C : Type*) [DecidableEq C] :
    (n : ℕ) → DecidableEq (History C n)
  | 0 => inferInstanceAs (DecidableEq PUnit)
  | n+1 => @instDecidableEqProd (History C n) C (historyDecidableEq C n) inferInstance

lemma history_card (C : Type*) [Fintype C] (n : ℕ) :
    Fintype.card (History C n) = (Fintype.card C)^n := by
  induction n with
  | zero =>
      calc
        _ = Fintype.card PUnit := Fintype.card_congr (Equiv.refl _)
        _ = _ := by rw [Fintype.card_punit, pow_zero]
  | succ n ih =>
      calc
        _ = Fintype.card (History C n × C) := Fintype.card_congr (Equiv.refl _)
        _ = _ := by rw [Fintype.card_prod, ih, pow_succ]

def transcript {P C : Type*} (c : ℕ → P → C) : (n : ℕ) → P → History C n
  | 0, _ => PUnit.unit
  | n+1, p => (transcript c n p,c n p)

noncomputable def transcriptKL {P C : Type*} [Fintype P] [Fintype C] [DecidableEq C]
    (p q : P × P → ℝ) (c : ℕ → P → C) (n : ℕ) : ℝ :=
  KL (push p (fun pr => (transcript c n pr.1,transcript c n pr.2)))
    (push q (fun pr => (transcript c n pr.1,transcript c n pr.2)))

lemma transcriptKL_zero {P C : Type*} [Fintype P] [Fintype C] [DecidableEq C]
    (p q : P × P → ℝ) (hp : ∑ pr, p pr = 1) (hq : ∑ pr, q pr = 1)
    (c : ℕ → P → C) : transcriptKL p q c 0 = 0 := by
  simp [transcriptKL, transcript, push, KL, hp, hq, History]

lemma transcriptKL_mono {P C : Type*} [Fintype P] [Fintype C] [DecidableEq C]
    (p q : P × P → ℝ) (hp : ∀ a, 0 ≤ p a) (hq : ∀ a, 0 ≤ q a)
    (hac : ∀ a, p a ≠ 0 → q a ≠ 0) (c : ℕ → P → C) (n : ℕ) :
    transcriptKL p q c n ≤ transcriptKL p q c (n+1) := by
  have hh := KL_refinement_nonneg p q hp hq hac
    (fun pr => (transcript c n pr.1,transcript c n pr.2))
    (fun pr => (c n pr.1,c n pr.2))
  change 0 ≤ KL (push p (observation (transcript c n) (c n)))
    (push q (observation (transcript c n) (c n))) - transcriptKL p q c n at hh
  rw [observation_entropy] at hh
  exact sub_nonneg.mp hh

theorem transcript_budget {P C : Type*} [Fintype P] [Fintype C] [DecidableEq C]
    (p q : P × P → ℝ) (hp : ∀ a, 0 ≤ p a) (hq : ∀ a, 0 ≤ q a)
    (hps : ∑ a, p a = 1) (hqs : ∑ a, q a = 1)
    (hac : ∀ a, p a ≠ 0 → q a ≠ 0) (c : ℕ → P → C) (K : ℕ) :
    (∑ n ∈ range K, (transcriptKL p q c (n+1)-transcriptKL p q c n)) ≤ KL p q := by
  have ht : (∑ n ∈ range K, (transcriptKL p q c (n+1)-transcriptKL p q c n)) =
      transcriptKL p q c K - transcriptKL p q c 0 := by
    induction K with
    | zero => simp
    | succ K ih => rw [sum_range_succ, ih]; ring
  rw [ht, transcriptKL_zero p q hps hqs c, sub_zero]
  exact KL_push_le p q hp hq hac _

section Marginal
variable {P Q : Type*} [Fintype P] [Fintype Q]
noncomputable def marginal (κ : Q → ℝ) (w : Q → P → ℝ) (p : P) : ℝ :=
  ∑ q, κ q * w q p

omit [Fintype P] in
lemma marginal_nonneg (κ : Q → ℝ) (w : Q → P → ℝ)
    (hκ : ∀ q, 0 ≤ κ q) (hw : ∀ q p, 0 ≤ w q p) (p : P) :
    0 ≤ marginal κ w p := sum_nonneg fun q _ => mul_nonneg (hκ q) (hw q p)

lemma marginal_sum (κ : Q → ℝ) (w : Q → P → ℝ)
    (hsκ : ∑ q, κ q = 1) (hsw : ∀ q, ∑ p, w q p = 1) :
    ∑ p, marginal κ w p = 1 := by
  unfold marginal
  rw [sum_comm]
  simp_rw [← mul_sum, hsw, mul_one]
  exact hsκ

omit [Fintype P] in
lemma wedge_ac (κ : Q → ℝ) (w : Q → P → ℝ)
    (hκ : ∀ q, 0 ≤ κ q) (hw : ∀ q p, 0 ≤ w q p) (pr : P × P) :
    wedge κ w pr ≠ 0 → marginal κ w pr.1 * marginal κ w pr.2 ≠ 0 := by
  intro hh
  apply mul_ne_zero
  · intro hz
    have ht := (sum_eq_zero_iff_of_nonneg (fun q _ => mul_nonneg (hκ q) (hw q pr.1))).mp hz
    apply hh
    apply sum_eq_zero
    intro q hq
    rw [ht q hq, zero_mul]
  · intro hz
    have ht := (sum_eq_zero_iff_of_nonneg (fun q _ => mul_nonneg (hκ q) (hw q pr.2))).mp hz
    apply hh
    apply sum_eq_zero
    intro q hq
    calc
      _ = (κ q * w q pr.2) * w q pr.1 := by ring
      _ = 0 := by rw [ht q hq, zero_mul]
end Marginal

lemma average_sq_le (K : ℕ) (hK : 0 < K) (f : ℕ → ℝ) :
    ((∑ n ∈ range K, f n)/(K:ℝ))^2 ≤ (∑ n ∈ range K, (f n)^2)/(K:ℝ) := by
  have hc := sum_sq_le_sum_mul_sum_of_sq_le_mul (R := ℝ) (range K)
    (r := f) (f := fun _ => (1:ℝ)) (g := fun n => (f n)^2)
    (fun _ _ => by norm_num) (fun _ _ => sq_nonneg _) (fun _ _ => by simp)
  simp only [sum_const, card_range, nsmul_eq_mul, mul_one] at hc
  have hk : (0:ℝ) < K := by exact_mod_cast hK
  rw [div_pow]
  apply (div_le_iff₀ (sq_pos_of_pos hk)).mpr
  calc
    _ ≤ (K:ℝ) * ∑ n ∈ range K, f n^2 := hc
    _ = _ := by field_simp

lemma average_sqrt_le (K : ℕ) (hK : 0 < K) (f : ℕ → ℝ)
    (hf : ∀ n ∈ range K, 0 ≤ f n) :
    (∑ n ∈ range K, sqrt (f n))/(K:ℝ) ≤ sqrt ((∑ n ∈ range K, f n)/(K:ℝ)) := by
  apply le_sqrt_of_sq_le
  convert average_sq_le K hK (fun n => sqrt (f n)) using 1
  congr 1
  apply sum_congr rfl
  intro n hn
  exact (sq_sqrt (hf n hn)).symm

section FrozenPrediction
variable {P Q C V : Type*} [Fintype P] [Fintype Q] [Fintype C] [DecidableEq C]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]

noncomputable def residual (μ : P → ℝ) (c : ℕ → P → C) (v : ℕ → C → V)
    (n : ℕ) (p : P) : V :=
  v n (c n p) - mean (push μ (fun p => (transcript c n p,c n p))) (v n) (transcript c n p)

noncomputable def discrepancy (κ : Q → ℝ) (w : Q → P → ℝ)
    (c : ℕ → P → C) (v : ℕ → C → V) (g : ℕ → Q → V) (n : ℕ) : ℝ :=
  |∑ q, κ q * ⟪∑ p, w q p • residual (marginal κ w) c v n p,g n q⟫_ℝ|

theorem frozen_prediction (κ : Q → ℝ) (w : Q → P → ℝ)
    (hκ : ∀ q, 0 ≤ κ q) (hw : ∀ q p, 0 ≤ w q p)
    (hsκ : ∑ q, κ q = 1) (hsw : ∀ q, ∑ p, w q p = 1)
    (c : ℕ → P → C) (v : ℕ → C → V) (g : ℕ → Q → V)
    {B B' : ℝ} (hB : 0 ≤ B) (hB' : 0 ≤ B')
    (hv : ∀ n c, ‖v n c‖ ≤ B) (hg : ∀ n q, ‖g n q‖ ≤ B')
    (K : ℕ) (hK : 0 < K) :
    (∑ n ∈ range K, discrepancy κ w c v g n)/(K:ℝ) ≤
      4*B*B'*sqrt (sqrt (KL (wedge κ w)
        (fun pr : P × P => marginal κ w pr.1 * marginal κ w pr.2)/(K:ℝ))) := by
  let pLaw := wedge κ w
  let μ := marginal κ w
  let qLaw : P × P → ℝ := fun pr => μ pr.1 * μ pr.2
  have hp := wedge_nonneg κ w hκ hw
  have hm := marginal_nonneg κ w hκ hw
  have hq : ∀ pr, 0 ≤ qLaw pr := fun pr => mul_nonneg (hm _) (hm _)
  have hps := wedge_sum κ w hsκ hsw
  have hms := marginal_sum κ w hsκ hsw
  have hqs : ∑ pr, qLaw pr = 1 := by
    dsimp [qLaw, μ]
    rw [Fintype.sum_prod_type, ← sum_mul_sum, hms, one_mul]
  have hac := wedge_ac κ w hκ hw
  let D := KL pLaw qLaw
  have hD : 0 ≤ D := KL_nonneg _ _ hp hq hps hqs hac
  let delta := fun n => transcriptKL pLaw qLaw c (n+1) - transcriptKL pLaw qLaw c n
  have hd : ∀ n, 0 ≤ delta n := fun n => sub_nonneg.mpr (transcriptKL_mono _ _ hp hq hac c n)
  have hbudget : (∑ n ∈ range K, delta n) ≤ D :=
    transcript_budget _ _ hp hq hps hqs hac c K
  let variance := fun n => ∑ q, κ q * ‖∑ p, w q p • residual μ c v n p‖^2
  have hvar : ∀ n, 0 ≤ variance n := fun n => sum_nonneg fun q _ => mul_nonneg (hκ q) (sq_nonneg _)
  have hcov : ∀ n, variance n ≤ 8*B^2*sqrt (delta n) := by
    intro n
    have hh := observation_covariance pLaw μ hp hm hps hac (transcript c n) (c n) (v n) hB (hv n)
    change |∑ pr, wedge κ w pr * ⟪residual μ c v n pr.1,residual μ c v n pr.2⟫_ℝ| ≤
      8*B^2*sqrt (delta n) at hh
    rw [wedge_square, abs_of_nonneg (hvar n)] at hh
    exact hh
  have hdisc : ∀ n, discrepancy κ w c v g n ≤ B' * sqrt (variance n) := by
    intro n
    exact weighted_inner_bound κ hκ hsκ _ (g n) hB' (hg n)
  have hk : (0:ℝ) < K := by exact_mod_cast hK
  have havar : (∑ n ∈ range K, variance n)/(K:ℝ) ≤ 8*B^2*sqrt (D/(K:ℝ)) := by
    calc
      _ ≤ (∑ n ∈ range K, 8*B^2*sqrt (delta n))/(K:ℝ) :=
        div_le_div_of_nonneg_right (sum_le_sum fun n _ => hcov n) hk.le
      _ = 8*B^2*((∑ n ∈ range K, sqrt (delta n))/(K:ℝ)) := by rw [← mul_sum]; ring
      _ ≤ 8*B^2*sqrt ((∑ n ∈ range K, delta n)/(K:ℝ)) :=
        mul_le_mul_of_nonneg_left (average_sqrt_le K hK delta (fun n _ => hd n)) (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (sqrt_le_sqrt (div_le_div_of_nonneg_right hbudget hk.le)) (by positivity)
  calc
    _ ≤ (∑ n ∈ range K, B'*sqrt (variance n))/(K:ℝ) :=
      div_le_div_of_nonneg_right (sum_le_sum fun n _ => hdisc n) hk.le
    _ = B'*((∑ n ∈ range K, sqrt (variance n))/(K:ℝ)) := by rw [← mul_sum]; ring
    _ ≤ B'*sqrt ((∑ n ∈ range K, variance n)/(K:ℝ)) :=
      mul_le_mul_of_nonneg_left (average_sqrt_le K hK variance (fun n _ => hvar n)) hB'
    _ ≤ B'*sqrt (8*B^2*sqrt (D/(K:ℝ))) := mul_le_mul_of_nonneg_left (sqrt_le_sqrt havar) hB'
    _ ≤ _ := by
      have hroot : sqrt (8*B^2*sqrt (D/(K:ℝ))) ≤ 4*B*sqrt (sqrt (D/(K:ℝ))) := by
        apply (sqrt_le_iff).mpr
        constructor
        · positivity
        · rw [mul_pow, mul_pow, sq_sqrt (sqrt_nonneg _)]
          nlinarith [mul_nonneg (sq_nonneg B) (sqrt_nonneg (D/(K:ℝ)))]
      simpa [mul_assoc, mul_left_comm, mul_comm, D, pLaw, qLaw, μ] using mul_le_mul_of_nonneg_left hroot hB'
end FrozenPrediction

section Posterior
variable {P H C V : Type*} [Fintype P] [Fintype H] [Fintype C]
  [DecidableEq H] [DecidableEq C] [NormedAddCommGroup V] [InnerProductSpace ℝ V]

noncomputable def posterior (μ : P → ℝ) (h : P → H) (x : H) (p : P) : ℝ :=
  (if h p = x then μ p else 0) / push μ h x

omit [Fintype H] in
lemma row_push_pair (μ : P → ℝ) (h : P → H) (c : P → C) :
    row (push μ (fun p => (h p,c p))) = push μ h := by
  exact row_refinement μ h c

omit [Fintype H] in

lemma mean_posterior (μ : P → ℝ) (h : P → H) (c : P → C) (v : C → V) (x : H) :
    mean (push μ (fun p => (h p,c p))) v x =
      ∑ p, posterior μ h x p • v (c p) := by
  unfold mean cond
  rw [row_push_pair]
  simp only [push, sum_div, sum_smul, Prod.mk.injEq]
  rw [sum_comm]
  apply sum_congr rfl
  intro p _
  by_cases he : h p = x <;> simp [he, posterior, push, ite_div, ite_smul]
end Posterior

section RandomTests
open MeasureTheory ProbabilityTheory
variable {Ω T H : Type*} [MeasurableSpace Ω] [MeasurableSpace T] [MeasurableSpace H]
  {ρ : Measure Ω} {ν : Measure T} [IsProbabilityMeasure ρ] [IsProbabilityMeasure ν]

lemma fresh_integral (u : Ω → H) (v : Ω → T) (hu : Measurable u) (hv : Measurable v)
    (hind : IndepFun u v ρ) (hlaw : ρ.map v = ν) (F : H × T → ℝ)
    (hF : Measurable F) (A : ℝ) (hbound : ∀ z, ‖F z‖ ≤ A) :
    (∫ ω, F (u ω,v ω) ∂ρ) = ∫ ω, ∫ t, F (u ω,t) ∂ν ∂ρ := by
  have hmap := hind.map_prod_eq_prod_map_map hu.aemeasurable hv.aemeasurable
  rw [hlaw] at hmap
  have hleft : (∫ ω, F (u ω,v ω) ∂ρ) = ∫ z, F z ∂((ρ.map u).prod ν) := by
    rw [← hmap, integral_map (hu.prodMk hv).aemeasurable hF.aestronglyMeasurable]
  rw [hleft]
  have hright : ((ρ.prod ν).map (fun z : Ω × T => (u z.1,z.2))) = (ρ.map u).prod ν := by
    calc
      _ = (ρ.prod ν).map (Prod.map u (id : T → T)) := by
        congr 1
      _ = (ρ.map u).prod (ν.map id) := (Measure.map_prod_map ρ ν hu measurable_id).symm
      _ = _ := by rw [Measure.map_id]
  have hpair : Measurable (fun z : Ω × T => (u z.1,z.2)) :=
    (hu.comp measurable_fst).prodMk measurable_snd
  rw [← hright, integral_map hpair.aemeasurable hF.aestronglyMeasurable]
  apply integral_prod
  apply Integrable.of_bound (hF.comp (hu.comp measurable_fst |>.prodMk measurable_snd)).aestronglyMeasurable A
  exact Filter.Eventually.of_forall fun z => hbound (u z.1,z.2)

lemma average_integral_bound (K : ℕ) (_hK : 0 < K) (F : ℕ → Ω → ℝ)
    (hF : ∀ n ∈ range K, Integrable (F n) ρ) (A : ℝ)
    (hb : ∀ ω, (∑ n ∈ range K, F n ω)/(K:ℝ) ≤ A) :
    (∑ n ∈ range K, ∫ ω, F n ω ∂ρ)/(K:ℝ) ≤ A := by
  have hi : Integrable (fun ω => (∑ n ∈ range K, F n ω)/(K:ℝ)) ρ :=
    (integrable_finsetSum _ hF).div_const _
  calc
    _ = ∫ ω, (∑ n ∈ range K, F n ω)/(K:ℝ) ∂ρ := by
      rw [integral_div, integral_finsetSum _ hF]
    _ ≤ ∫ _, A ∂ρ := integral_mono hi (integrable_const A) hb
    _ = A := by simp
end RandomTests

section HistoriesMeasurable
open MeasureTheory ProbabilityTheory
universe uC
variable {C : Type uC} [MeasurableSpace C]

instance historyMeasurable : (n : ℕ) → MeasurableSpace (History C n)
  | 0 => inferInstanceAs (MeasurableSpace PUnit)
  | n+1 => by
    letI : MeasurableSpace (History C n) := historyMeasurable n
    exact inferInstanceAs (MeasurableSpace (History C n × C))

omit [MeasurableSpace C] in
lemma transcript_congr {P : Type*} (c d : ℕ → P → C) (n : ℕ)
    (hc : ∀ k < n, c k = d k) : transcript c n = transcript d n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    funext p
    change (transcript c n p,c n p) = (transcript d n p,d n p)
    rw [ih (fun k hk => hc k (Nat.lt_succ_of_lt hk)), hc n (Nat.lt_succ_self n)]

lemma measurable_transcript {Ω P : Type*} [MeasurableSpace Ω]
    (c : ℕ → Ω → P → C) (hc : ∀ n p, Measurable (fun ω => c n ω p)) (n : ℕ) :
    Measurable (fun ω p => transcript (fun k => c k ω) n p) := by
  induction n with
  | zero =>
    change Measurable (fun _ : Ω => (fun _ : P => PUnit.unit))
    exact measurable_const
  | succ n ih =>
    apply Measurable.of_eval
    intro p
    exact ((measurable_pi_apply p).comp ih).prodMk (hc n p)

lemma prefix_independent {Ω P T : Type*} [MeasurableSpace Ω] [MeasurableSpace T]
    {ρ : Measure Ω} (tests : ℕ → Ω → T) (ht : ∀ n, Measurable (tests n))
    (hind : iIndepFun tests ρ) (t0 : T) (c : T → P → C)
    (hc : ∀ p, Measurable (fun t => c t p)) (n : ℕ) :
    IndepFun (fun ω p => transcript (fun k => c (tests k ω)) n p) (tests n) ρ := by
  classical
  let extend : ((range n) → T) → ℕ → T :=
    fun v k => if hk : k ∈ range n then v ⟨k,hk⟩ else t0
  have he : ∀ k, Measurable (fun v => extend v k) := by
    intro k
    by_cases hk : k ∈ range n
    · simpa only [extend, dite_eq_left hk] using
        (measurable_pi_apply (⟨k,hk⟩ : range n) : Measurable (fun v : range n → T => v ⟨k,hk⟩))
    · simpa only [extend, dite_eq_right hk] using (measurable_const : Measurable (fun _ : range n → T => t0))
  let F : ((range n) → T) → P → History C n :=
    fun v p => transcript (fun k => c (extend v k)) n p
  have hF : Measurable F := measurable_transcript _ (fun k p => (hc p).comp (he k)) n
  have hi := (hind.indepFun_finset (range n) {n} (by simp) ht).comp hF
    (measurable_pi_apply (⟨n,mem_singleton_self n⟩ : ({n} : Finset ℕ)))
  have heq : (fun ω => F (fun i : range n => tests i ω)) =
      (fun ω p => transcript (fun k => c (tests k ω)) n p) := by
    funext ω
    apply transcript_congr
    intro k hk
    simp only [extend, mem_range.mpr hk, dite_true]
  change IndepFun (fun ω => F (fun i : range n => tests i ω)) (tests n) ρ at hi
  rw [heq] at hi
  exact hi
end HistoriesMeasurable

section RandomDevice
open MeasureTheory ProbabilityTheory
variable {P Q C V : Type*} [Fintype P] [Fintype Q] [Fintype C] [DecidableEq C]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]

lemma norm_convex_sum_le {A : Type*} [Fintype A] (a : A → ℝ)
    (ha : ∀ i, 0 ≤ a i) (hs : ∑ i, a i = 1) (u : A → V) {R : ℝ}
    (hu : ∀ i, ‖u i‖ ≤ R) : ‖∑ i, a i • u i‖ ≤ R := by
  calc
    _ ≤ ∑ i, ‖a i • u i‖ := norm_sum_le _ _
    _ = ∑ i, a i * ‖u i‖ := by simp [norm_smul, Real.norm_eq_abs, abs_of_nonneg, ha]
    _ ≤ ∑ i, a i * R := sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hu i) (ha i)
    _ = R := by rw [← sum_mul, hs, one_mul]

noncomputable def testDiscrepancy {H : Type*} [Fintype H] [DecidableEq H]
    (κ : Q → ℝ) (w : Q → P → ℝ) (h : P → H) (c : P → C) (v : C → V) (g : Q → V) : ℝ :=
  |∑ q, κ q * ⟪∑ p, w q p •
    (v (c p) - mean (push (marginal κ w) (fun p => (h p,c p))) v (h p)),g q⟫_ℝ|

lemma testDiscrepancy_bound {H : Type*} [Fintype H] [DecidableEq H]
    (κ : Q → ℝ) (w : Q → P → ℝ) (hκ : ∀ q, 0 ≤ κ q) (hw : ∀ q p, 0 ≤ w q p)
    (hsκ : ∑ q, κ q = 1) (hsw : ∀ q, ∑ p, w q p = 1)
    (h : P → H) (c : P → C) (v : C → V) (g : Q → V)
    {B B' : ℝ} (hB : 0 ≤ B) (_hB' : 0 ≤ B')
    (hv : ∀ c, ‖v c‖ ≤ B) (hg : ∀ q, ‖g q‖ ≤ B') :
    ‖testDiscrepancy κ w h c v g‖ ≤ 2*B*B' := by
  let u := fun p => v (c p) - mean (push (marginal κ w) (fun p => (h p,c p))) v (h p)
  have hu : ∀ p, ‖u p‖ ≤ 2*B := by
    intro p
    have hh := norm_mean_le (push (marginal κ w) (fun p => (h p,c p)))
      (push_nonneg (marginal_nonneg κ w hκ hw) _) v hB hv (h p)
    exact (norm_sub_le _ _).trans (by linarith [hv (c p)])
  have hqu : ∀ q, ‖∑ p, w q p • u p‖ ≤ 2*B := fun q =>
    norm_convex_sum_le _ (hw q) (hsw q) u hu
  rw [testDiscrepancy, Real.norm_eq_abs, abs_abs]
  calc
    _ ≤ ∑ q, |κ q * ⟪∑ p, w q p • u p,g q⟫_ℝ| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ q, κ q * (2*B*B') := by
      apply sum_le_sum
      intro q _
      rw [abs_mul, abs_of_nonneg (hκ q)]
      apply mul_le_mul_of_nonneg_left _ (hκ q)
      exact (abs_real_inner_le_norm _ _).trans (mul_le_mul (hqu q) (hg q) (norm_nonneg _) (by positivity))
    _ = _ := by rw [← sum_mul, hsκ, one_mul]

variable [MeasurableSpace C]
variable {Ω T : Type*} [MeasurableSpace Ω] [MeasurableSpace T]
  {ρ : Measure Ω} {ν : Measure T} [IsProbabilityMeasure ρ] [IsProbabilityMeasure ν]

theorem random_prediction (κ : Q → ℝ) (w : Q → P → ℝ)
    (hκ : ∀ q, 0 ≤ κ q) (hw : ∀ q p, 0 ≤ w q p)
    (hsκ : ∑ q, κ q = 1) (hsw : ∀ q, ∑ p, w q p = 1)
    (tests : ℕ → Ω → T) (ht : ∀ n, Measurable (tests n))
    (hind : iIndepFun tests ρ) (hlaw : ∀ n, ρ.map (tests n) = ν) (t0 : T)
    (c : T → P → C) (v : T → C → V) (g : T → Q → V)
    (hc : ∀ p, Measurable (fun t => c t p))
    (hδ : ∀ n, Measurable (fun z : (P → History C n) × T =>
      testDiscrepancy κ w z.1 (c z.2) (v z.2) (g z.2)))
    {B B' : ℝ} (hB : 0 ≤ B) (hB' : 0 ≤ B')
    (hv : ∀ t c, ‖v t c‖ ≤ B) (hg : ∀ t q, ‖g t q‖ ≤ B')
    (K : ℕ) (hK : 0 < K) :
    (∑ n ∈ range K, ∫ ω, ∫ t, testDiscrepancy κ w
      (transcript (fun k => c (tests k ω)) n) (c t) (v t) (g t) ∂ν ∂ρ)/(K:ℝ) ≤
      4*B*B'*sqrt (sqrt (KL (wedge κ w)
        (fun pr : P × P => marginal κ w pr.1 * marginal κ w pr.2)/(K:ℝ))) := by
  let H := fun n ω p => transcript (fun k => c (tests k ω)) n p
  let δ := fun n (z : (P → History C n) × T) =>
    testDiscrepancy κ w z.1 (c z.2) (v z.2) (g z.2)
  have hH : ∀ n, Measurable (H n) := fun n =>
    measurable_transcript _ (fun k p => (hc p).comp (ht k)) n
  have hb : ∀ n z, ‖δ n z‖ ≤ 2*B*B' := fun n z =>
    testDiscrepancy_bound κ w hκ hw hsκ hsw z.1 (c z.2) (v z.2) (g z.2) hB hB' (hv z.2) (hg z.2)
  have hfresh (n : ℕ) : (∫ ω, δ n (H n ω,tests n ω) ∂ρ) =
      ∫ ω, ∫ t, δ n (H n ω,t) ∂ν ∂ρ :=
    fresh_integral (H n) (tests n) (hH n) (ht n)
      (prefix_independent tests ht hind t0 c hc n) (hlaw n) (δ n) (hδ n) _ (hb n)
  change (∑ n ∈ range K, ∫ ω, ∫ t, δ n (H n ω,t) ∂ν ∂ρ)/(K:ℝ) ≤ _
  simp_rw [← hfresh]
  apply average_integral_bound K hK
  · intro n _
    exact Integrable.of_bound ((hδ n).comp ((hH n).prodMk (ht n))).aestronglyMeasurable _
      (Filter.Eventually.of_forall fun ω => hb n (H n ω,tests n ω))
  · intro ω
    exact frozen_prediction κ w hκ hw hsκ hsw
      (fun n => c (tests n ω)) (fun n => v (tests n ω)) (fun n => g (tests n ω))
      hB hB' (fun n => hv (tests n ω)) (fun n => hg (tests n ω)) K hK

lemma sqrt_sqrt_eq_quarter {x : ℝ} (hx : 0 ≤ x) : sqrt (sqrt x) = x ^ (1/4:ℝ) := by
  rw [sqrt_eq_rpow, sqrt_eq_rpow, ← rpow_mul hx]
  norm_num

theorem exists_prediction_history [Nonempty C]
    (κ : Q → ℝ) (w : Q → P → ℝ)
    (hκ : ∀ q, 0 ≤ κ q) (hw : ∀ q p, 0 ≤ w q p)
    (hsκ : ∑ q, κ q = 1) (hsw : ∀ q, ∑ p, w q p = 1)
    (c : T → P → C) (v : T → C → V) (g : T → Q → V)
    (hc : ∀ p, Measurable (fun t => c t p))
    (hδ : ∀ n, Measurable (fun z : (P → History C n) × T =>
      testDiscrepancy κ w z.1 (c z.2) (v z.2) (g z.2)))
    {B B' : ℝ} (hB : 0 ≤ B) (hB' : 0 ≤ B')
    (hv : ∀ t c, ‖v t c‖ ≤ B) (hg : ∀ t q, ‖g t q‖ ≤ B')
    (K : ℕ) (hK : 0 < K) :
    ∃ n < K, ∃ h : P → History C n,
      (univ.image h).card ≤ (Fintype.card C)^(K-1) ∧
      (∫ t, testDiscrepancy κ w h (c t) (v t) (g t) ∂ν) ≤
        4*B*B'*(KL (wedge κ w)
          (fun pr : P × P => marginal κ w pr.1 * marginal κ w pr.2)/(K:ℝ))^(1/4:ℝ) := by
  classical
  let ρ : Measure (ℕ → T) := Measure.infinitePi (fun _ : ℕ => ν)
  let tests := fun n (ω : ℕ → T) => ω n
  have ht : ∀ n, Measurable (tests n) := fun n => measurable_pi_apply n
  have hind : iIndepFun tests ρ := iIndepFun_infinitePi (fun _ => measurable_id)
  have hlaw : ∀ n, ρ.map (tests n) = ν := fun n =>
    (measurePreserving_eval_infinitePi (fun _ : ℕ => ν) n).map_eq
  let t0 : T := Classical.choice (nonempty_of_isProbabilityMeasure ν)
  have hpred := random_prediction κ w hκ hw hsκ hsw tests ht hind hlaw t0 c v g hc hδ
    hB hB' hv hg K hK
  have hD : 0 ≤ KL (wedge κ w) (fun pr : P × P => marginal κ w pr.1 * marginal κ w pr.2) := by
    have hm := marginal_nonneg κ w hκ hw
    have hs := marginal_sum κ w hsκ hsw
    apply KL_nonneg _ _ (wedge_nonneg κ w hκ hw) (fun pr => mul_nonneg (hm _) (hm _))
      (wedge_sum κ w hsκ hsw) _ (wedge_ac κ w hκ hw)
    rw [Fintype.sum_prod_type, ← sum_mul_sum, hs, one_mul]
  rw [sqrt_sqrt_eq_quarter (div_nonneg hD (Nat.cast_nonneg K))] at hpred
  let R := 4*B*B'*(KL (wedge κ w)
    (fun pr : P × P => marginal κ w pr.1 * marginal κ w pr.2)/(K:ℝ))^(1/4:ℝ)
  let H := fun n ω p => transcript (fun k => c (tests k ω)) n p
  let F := fun n (ω : ℕ → T) => ∫ t, testDiscrepancy κ w (H n ω) (c t) (v t) (g t) ∂ν
  have hsum : (∑ n ∈ range K, ∫ ω, F n ω ∂ρ) ≤ ∑ _ ∈ range K, R := by
    have he := (div_le_iff₀ (show (0:ℝ) < K by exact_mod_cast hK)).mp hpred
    simpa only [sum_const, card_range, nsmul_eq_mul, mul_comm, R, F, H] using he
  obtain ⟨n,hn,hnb⟩ := exists_le_of_sum_le (nonempty_range_iff.mpr (Nat.ne_of_gt hK)) hsum
  have hH : Measurable (H n) := measurable_transcript _ (fun k p => (hc p).comp (ht k)) n
  have hpair : Measurable (fun z : (ℕ → T) × T => (H n z.1,z.2)) :=
    (hH.comp measurable_fst).prodMk measurable_snd
  have hi : Integrable (fun z : (ℕ → T) × T =>
      testDiscrepancy κ w (H n z.1) (c z.2) (v z.2) (g z.2)) (ρ.prod ν) :=
    Integrable.of_bound ((hδ n).comp hpair).aestronglyMeasurable (2*B*B')
      (Filter.Eventually.of_forall fun z => testDiscrepancy_bound κ w hκ hw hsκ hsw
        (H n z.1) (c z.2) (v z.2) (g z.2) hB hB' (hv z.2) (hg z.2))
  obtain ⟨ω,hω⟩ := exists_le_integral hi.integral_prod_left
  have hn' : n < K := mem_range.mp hn
  refine ⟨n,hn',H n ω,?_,hω.trans hnb⟩
  calc
    _ ≤ Fintype.card (History C n) := card_le_univ _
    _ = (Fintype.card C)^n := history_card C n
    _ ≤ _ := Nat.pow_le_pow_right Fintype.card_pos (by omega)
end RandomDevice

end PlanarUnitDistances.FiniteInformation

end OAI
