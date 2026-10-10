import Mathlib

namespace OAI

namespace MetricKMedianRecovery.Dyadic
variable {A : Type*} [Fintype A] [DecidableEq A]

noncomputable def rawCount (p : A → ℝ) (b : ℕ) (a : A) : ℕ :=
  Nat.floor ((2:ℝ)^b * p a)

omit [DecidableEq A] in
lemma rawCount_sum_le (p : A → ℝ) (hp : ∀ a, 0 ≤ p a)
    (ht : ∑ a, p a = 1) (b : ℕ) : (∑ a, rawCount p b a) ≤ 2^b := by
  have h := Finset.sum_le_sum (s := (Finset.univ : Finset A))
    (fun a _ => Nat.floor_le (mul_nonneg (by positivity : (0:ℝ) ≤ 2^b) (hp a)))
  rw [← Finset.mul_sum,ht,mul_one] at h
  unfold rawCount
  exact_mod_cast h

noncomputable def count (p : A → ℝ) (b : ℕ) (default a : A) : ℕ :=
  rawCount p b a + if a = default then 2^b - ∑ a, rawCount p b a else 0

lemma count_ge (p : A → ℝ) (b : ℕ) (default a : A) : rawCount p b a ≤ count p b default a := by
  unfold count
  omega

lemma count_total (p : A → ℝ) (hp : ∀ a, 0 ≤ p a)
    (ht : ∑ a, p a = 1) (b : ℕ) (default : A) : ∑ a, count p b default a = 2^b := by
  have h := rawCount_sum_le p hp ht b
  simp only [count,Finset.sum_add_distrib,Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  omega

noncomputable def weight (p : A → ℝ) (b : ℕ) (default a : A) : ℝ :=
  (count p b default a : ℝ) / 2^b

lemma weight_nonneg (p : A → ℝ) (b : ℕ) (default a : A) : 0 ≤ weight p b default a := by
  unfold weight
  positivity

lemma weight_total (p : A → ℝ) (hp : ∀ a, 0 ≤ p a)
    (ht : ∑ a, p a = 1) (b : ℕ) (default : A) : ∑ a, weight p b default a = 1 := by
  simp only [weight,← Finset.sum_div,← Nat.cast_sum,count_total p hp ht b default,Nat.cast_pow,Nat.cast_ofNat]
  exact div_self (by positivity)

lemma weight_lower (p : A → ℝ) (hp : ∀ a, 0 ≤ p a) (b : ℕ) (default a : A)
    (hb : ∀ a, 0 < p a → 2 ≤ (2:ℝ)^b * p a) : p a / 2 ≤ weight p b default a := by
  by_cases ha : p a = 0
  · rw [ha,zero_div]
    exact weight_nonneg p b default a
  · have ha' : 0 < p a := lt_of_le_of_ne (hp a) (Ne.symm ha)
    have hh := hb a ha'
    have hf := Nat.lt_floor_add_one ((2:ℝ)^b * p a)
    have hc : (rawCount p b a : ℝ) ≤ count p b default a := Nat.cast_le.mpr (count_ge p b default a)
    change p a / 2 ≤ (count p b default a : ℝ) / 2^b
    apply (le_div_iff₀ (by positivity : (0:ℝ) < 2^b)).mpr
    change (2:ℝ)^b * p a < (rawCount p b a : ℝ) + 1 at hf
    nlinarith

omit [DecidableEq A] in
lemma exists_precision (p : A → ℝ) : ∃ b : ℕ, ∀ a, 0 < p a → 2 ≤ (2:ℝ)^b * p a := by
  classical
  have hh : ∀ a, ∃ b : ℕ, 0 < p a → 2 ≤ (2:ℝ)^b * p a := by
    intro a
    by_cases ha : 0 < p a
    · obtain ⟨b,hb⟩ := pow_unbounded_of_one_lt (2/p a) (by norm_num : (1:ℝ)<2)
      refine ⟨b,fun _ => ?_⟩
      exact ((div_lt_iff₀ ha).mp hb).le
    · exact ⟨0,fun h => (ha h).elim⟩
  choose n hn using hh
  refine ⟨∑ a, n a,fun a ha => ?_⟩
  have hnle : n a ≤ ∑ a, n a := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ a)
  exact (hn a ha).trans (mul_le_mul_of_nonneg_right
    (pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) hnle) ha.le)

noncomputable def allocation (p : A → ℝ) (hp : ∀ a, 0 ≤ p a)
    (ht : ∑ a, p a = 1) (b : ℕ) (default : A) :
    (Fin b → Bool) ≃ (Σ a, Fin (count p b default a)) :=
  Fintype.equivOfCardEq (by
    simpa only [Fintype.card_fun,Fintype.card_bool,Fintype.card_fin,Fintype.card_sigma]
      using (count_total p hp ht b default).symm)

noncomputable def draw (p : A → ℝ) (hp : ∀ a, 0 ≤ p a)
    (ht : ∑ a, p a = 1) (b : ℕ) (default : A) (bits : Fin b → Bool) : A :=
  (allocation p hp ht b default bits).1

lemma draw_average (p : A → ℝ) (hp : ∀ a, 0 ≤ p a)
    (ht : ∑ a, p a = 1) (b : ℕ) (default : A) (f : A → ℝ) :
    (∑ bits : Fin b → Bool, f (draw p hp ht b default bits)) / 2^b =
      ∑ a, weight p b default a * f a := by
  have h := Fintype.sum_equiv (allocation p hp ht b default)
    (fun bits => f (draw p hp ht b default bits)) (fun x => f x.1) (fun _ => rfl)
  rw [h,Fintype.sum_sigma,Finset.sum_div]
  apply Finset.sum_congr rfl
  intro a _
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,weight]
  ring

lemma draw_probability (p : A → ℝ) (hp : ∀ a, 0 ≤ p a)
    (ht : ∑ a, p a = 1) (b : ℕ) (default a : A) :
    (∑ bits : Fin b → Bool, if draw p hp ht b default bits = a then (1:ℝ) else 0) / 2^b =
      weight p b default a := by
  have h := draw_average p hp ht b default (fun x => if x = a then (1:ℝ) else 0)
  simpa only [mul_ite,mul_one,mul_zero,Finset.sum_ite_eq',Finset.mem_univ,ite_true] using h

end MetricKMedianRecovery.Dyadic

end OAI
