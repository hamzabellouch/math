import Mathlib

namespace OAI

namespace SharpRamseyFive.FiniteEntropy
open scoped BigOperators Classical

structure Law (α : Type*) [Fintype α] where
  mass : α → ℝ
  nonneg : ∀ a,0 ≤ mass a
  sum_one : ∑ a,mass a = 1

instance {α : Type*} [Fintype α] : CoeFun (Law α) (fun _ => α → ℝ) := ⟨Law.mass⟩

variable {α β : Type*} [Fintype α] [Fintype β]

noncomputable def entropy (p : α → ℝ) : ℝ := -∑ a,p a*Real.log (p a)
noncomputable def divergence (p q : α → ℝ) : ℝ := ∑ a,p a*Real.log (p a/q a)

lemma mass_le_one (p : Law α) (a : α) : p a ≤ 1 := by
  rw [←p.sum_one]
  exact Finset.single_le_sum (fun b _ => p.nonneg b) (Finset.mem_univ a)

lemma entropy_nonneg (p : Law α) : 0 ≤ entropy p := by
  unfold entropy
  apply neg_nonneg.mpr
  apply Finset.sum_nonpos
  intro a _
  by_cases h : p a=0
  · simp [h]
  · exact mul_nonpos_of_nonneg_of_nonpos (p.nonneg a)
      (Real.log_nonpos ((lt_of_le_of_ne (p.nonneg a) (Ne.symm h)).le) (mass_le_one p a))

lemma atom_bound_entropy (p : Law α) (A : ℝ)
    (hpa : ∀ a,p a ≤ A) : -Real.log A ≤ entropy p := by
  have hsum : (∑ a,p a*Real.log (p a)) ≤ Real.log A := by
    calc
      _ ≤ ∑ a,p a*Real.log A := Finset.sum_le_sum fun a _ => by
        by_cases h : p a=0
        · simp [h]
        · exact mul_le_mul_of_nonneg_left
            (Real.log_le_log (lt_of_le_of_ne (p.nonneg a) (Ne.symm h)) (hpa a)) (p.nonneg a)
      _ = Real.log A := by rw [←Finset.sum_mul,p.sum_one,one_mul]
  exact neg_le_neg hsum

lemma point_log_ratio (p q : ℝ) (hp : 0 ≤ p) (hq : 0 ≤ q)
    (hpq : 0 < p → 0 < q) : p-q ≤ p*Real.log (p/q) := by
  by_cases h : p=0
  · simp [h,hq]
  · have hp' : 0 < p := lt_of_le_of_ne hp (Ne.symm h)
    have hq' := hpq hp'
    have hl := Real.log_le_sub_one_of_pos (div_pos hq' hp')
    have hm := mul_le_mul_of_nonneg_left hl hp
    rw [Real.log_div (ne_of_gt hq') (ne_of_gt hp')] at hm
    rw [Real.log_div h (ne_of_gt hq')]
    have he : p*(q/p-1)=q-p := by field_simp
    rw [he] at hm
    nlinarith

theorem divergence_nonneg (p q : Law α) (hpq : ∀ a,0 < p a → 0 < q a) :
    0 ≤ divergence p q := by
  have h := Finset.sum_le_sum (fun a (_ : a ∈ Finset.univ) =>
    point_log_ratio (p a) (q a) (p.nonneg a) (q.nonneg a) (hpq a))
  simpa only [Finset.sum_sub_distrib,p.sum_one,q.sum_one,sub_self,divergence] using h

theorem entropy_le_log_card (p : Law α) : entropy p ≤ Real.log (Fintype.card α) := by
  have hne : Nonempty α := by
    by_contra h
    have : IsEmpty α := not_nonempty_iff.mp h
    simpa using p.sum_one
  let := hne
  have hc : 0 < (Fintype.card α:ℝ) := by exact_mod_cast Fintype.card_pos
  let u : Law α := ⟨fun _ => 1/Fintype.card α,fun _ => by positivity,by simp [ne_of_gt hc]⟩
  have hd := divergence_nonneg p u (fun _ _ => by dsimp [u]; positivity)
  have he : divergence p u = -entropy p+Real.log (Fintype.card α) := by
    unfold divergence entropy
    calc
      _ = ∑ a,(p a*Real.log (p a)+p a*Real.log (Fintype.card α)) := by
        apply Finset.sum_congr rfl
        intro a _
        by_cases h : p a=0
        · simp [h]
        · dsimp [u]
          rw [div_div_eq_mul_div,div_one,Real.log_mul h (ne_of_gt hc)]
          ring
      _ = _ := by rw [Finset.sum_add_distrib,←Finset.sum_mul,p.sum_one]; ring
  linarith

theorem divergence_test (p q : Law α) (hpq : ∀ a,0 < p a → 0 < q a)
    (f : α → ℝ) :
    (∑ a,p a*f a)+1-(∑ a,q a*Real.exp (f a)) ≤ divergence p q := by
  have hpw (a : α) : p a*f a+p a-q a*Real.exp (f a) ≤
      p a*Real.log (p a/q a) := by
    have h := point_log_ratio (p a) (q a*Real.exp (f a)) (p.nonneg a)
      (mul_nonneg (q.nonneg a) (Real.exp_pos _).le)
      (fun hp => mul_pos (hpq a hp) (Real.exp_pos _))
    by_cases hz : p a=0
    · simp only [hz,zero_mul,zero_add] at h ⊢
      exact h
    · have hq : q a ≠ 0 := ne_of_gt (hpq a (lt_of_le_of_ne (p.nonneg a) (Ne.symm hz)))
      rw [Real.log_div hz (mul_ne_zero hq (Real.exp_ne_zero _)),
        Real.log_mul hq (Real.exp_ne_zero _),Real.log_exp] at h
      rw [Real.log_div hz hq]
      nlinarith
  have hs := Finset.sum_le_sum (fun a (_ : a∈Finset.univ) => hpw a)
  simpa only [Finset.sum_sub_distrib,Finset.sum_add_distrib,p.sum_one,divergence] using hs

theorem event_comparison (p q : Law α) (hpq : ∀ a,0 < p a → 0 < q a)
    (E : Finset α) : (∑ a∈E,q a) ≤ 2*(divergence p q+∑ a∈E,p a) := by
  classical
  have ht := divergence_test p q hpq (fun a => if a∈E then -1 else 0)
  have he1 : (∑ a,p a*(if a∈E then -1 else 0)) = -(∑ a∈E,p a) := by
    simp only [mul_ite,mul_neg_one,mul_zero,←Finset.sum_filter,Finset.filter_univ_mem,Finset.sum_neg_distrib]
  have he2 : (∑ a,q a*Real.exp (if a∈E then -1 else 0)) =
      1-(1-Real.exp (-1))*(∑ a∈E,q a) := by
    have he (a : α) : q a*Real.exp (if a∈E then -1 else 0) =
        q a-(1-Real.exp (-1))*(if a∈E then q a else 0) := by
      split_ifs
      · ring
      · simp
    simp only [he,Finset.sum_sub_distrib,←Finset.mul_sum,q.sum_one,←Finset.sum_filter,
      Finset.filter_univ_mem]
  rw [he1,he2] at ht
  have hhalf : Real.exp (-1) ≤ (1/2:ℝ) := by
    rw [Real.exp_neg]
    have he : (2:ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1:ℝ)]
    simpa only [one_div] using one_div_le_one_div_of_le (by norm_num : (0:ℝ)<2) he
  have hqE : 0 ≤ ∑ a∈E,q a := Finset.sum_nonneg fun a _ => q.nonneg a
  nlinarith

noncomputable def first (p : Law (α × β)) : Law α where
  mass a := ∑ b,p (a,b)
  nonneg a := Finset.sum_nonneg fun b _ => p.nonneg (a,b)
  sum_one := by rw [←Fintype.sum_prod_type]; exact p.sum_one

noncomputable def second (p : Law (α × β)) : Law β where
  mass b := ∑ a,p (a,b)
  nonneg b := Finset.sum_nonneg fun a _ => p.nonneg (a,b)
  sum_one := by rw [Finset.sum_comm,←Fintype.sum_prod_type]; exact p.sum_one

noncomputable def product (p : Law α) (q : Law β) : Law (α × β) where
  mass z := p z.1*q z.2
  nonneg z := mul_nonneg (p.nonneg _) (q.nonneg _)
  sum_one := by rw [Fintype.sum_prod_type]; simp only [←Finset.mul_sum,q.sum_one,mul_one,p.sum_one]

lemma le_first (p : Law (α × β)) (a : α) (b : β) : p (a,b) ≤ first p a :=
  Finset.single_le_sum (fun c _ => p.nonneg (a,c)) (Finset.mem_univ b)
lemma le_second (p : Law (α × β)) (a : α) (b : β) : p (a,b) ≤ second p b :=
  Finset.single_le_sum (fun c _ => p.nonneg (c,b)) (Finset.mem_univ a)

lemma ac_product (p : Law (α × β)) (z : α × β) (hz : 0 < p z) :
    0 < product (first p) (second p) z :=
  mul_pos (hz.trans_le (le_first p _ _)) (hz.trans_le (le_second p _ _))

theorem mutual_information (p : Law (α × β)) :
    divergence p (product (first p) (second p)) =
      entropy (first p)+entropy (second p)-entropy p := by
  have hterm (z : α × β) : p z*Real.log (p z/product (first p) (second p) z) =
      p z*Real.log (p z)-p z*Real.log (first p z.1)-p z*Real.log (second p z.2) := by
    by_cases hz : p z=0
    · simp [hz]
    · have hp : 0 < p z := lt_of_le_of_ne (p.nonneg z) (Ne.symm hz)
      have h1 : first p z.1 ≠ 0 := ne_of_gt (hp.trans_le (le_first p _ _))
      have h2 : second p z.2 ≠ 0 := ne_of_gt (hp.trans_le (le_second p _ _))
      change _ = _
      dsimp [product]
      rw [Real.log_div hz (mul_ne_zero h1 h2),Real.log_mul h1 h2]
      ring
  have hs1 : (∑ z : α × β,p z*Real.log (first p z.1)) =
      ∑ a,first p a*Real.log (first p a) := by
    rw [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro a _
    dsimp only
    rw [←Finset.sum_mul]
    rfl
  have hs2 : (∑ z : α × β,p z*Real.log (second p z.2)) =
      ∑ b,second p b*Real.log (second p b) := by
    rw [Fintype.sum_prod_type,Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro b _
    dsimp only
    rw [←Finset.sum_mul]
    rfl
  simp only [divergence,hterm,Finset.sum_sub_distrib,hs1,hs2,entropy]
  ring

lemma entropy_subadditive (p : Law (α × β)) :
    entropy p ≤ entropy (first p)+entropy (second p) := by
  have := divergence_nonneg p (product (first p) (second p)) (ac_product p)
  rw [mutual_information] at this
  linarith

end SharpRamseyFive.FiniteEntropy

end OAI
