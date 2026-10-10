import Mathlib
import OAI.Combinatorics.MatchingCount.Probability.LocalVariance

namespace OAI

namespace MatchingFPRAS.Replica

section

open Finset

variable {R A S : Type*} [Fintype R] [Fintype A] [Fintype S] [DecidableEq S]

noncomputable def pushedFlow (ρ : R → ℝ) (F : R → A → S) (q : A → A → ℝ) (s t : S) : ℝ :=
  ∑ z : R × (A × A), if (F z.1 z.2.1,F z.1 z.2.2) = (s,t) then ρ z.1*q z.2.1 z.2.2 else 0

omit [Fintype S] in
lemma pushedFlow_nonneg (ρ : R → ℝ) (F : R → A → S) (q : A → A → ℝ)
    (hρ : ∀ r, 0 ≤ ρ r) (hq : ∀ a b, 0 ≤ q a b) (s t : S) :
    0 ≤ pushedFlow ρ F q s t := by
  apply Finset.sum_nonneg; intro z _
  split_ifs <;> [exact mul_nonneg (hρ _) (hq _ _); exact le_refl _]

lemma pushedFlow_test (ρ : R → ℝ) (F : R → A → S) (q : A → A → ℝ)
    (g : S → S → ℝ) :
    (∑ s, ∑ t, pushedFlow ρ F q s t*g s t) =
    ∑ r, ρ r*∑ a, ∑ b, q a b*g (F r a) (F r b) := by
  classical
  calc
    _ = ∑ st : S × S, (∑ z : R × (A × A),
        if (F z.1 z.2.1,F z.1 z.2.2) = st then ρ z.1*q z.2.1 z.2.2 else 0)*g st.1 st.2 := by
      rw [Fintype.sum_prod_type]; rfl
    _ = ∑ z : R × (A × A), ρ z.1*q z.2.1 z.2.2*g (F z.1 z.2.1) (F z.1 z.2.2) := by
      simp_rw [Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl; intro z _
      simp only [ite_mul,zero_mul]
      simp
    _ = _ := by
      simp only [Fintype.sum_prod_type,Finset.mul_sum]
      apply Finset.sum_congr rfl; intro r _
      apply Finset.sum_congr rfl; intro a _
      apply Finset.sum_congr rfl; intro b _
      ring

lemma pushedFlow_row_test (ρ : R → ℝ) (F : R → A → S) (q : A → A → ℝ)
    (μ : A → ℝ) (hrow : ∀ a, ∑ b, q a b = μ a) (g : S → ℝ) :
    (∑ s, ∑ t, pushedFlow ρ F q s t*g s) = ∑ r, ρ r*∑ a, μ a*g (F r a) := by
  rw [pushedFlow_test]
  apply Finset.sum_congr rfl; intro r _
  congr 1
  apply Finset.sum_congr rfl; intro a _
  rw [← Finset.sum_mul,hrow]

lemma pushedFlow_col_test (ρ : R → ℝ) (F : R → A → S) (q : A → A → ℝ)
    (μ : A → ℝ) (hcol : ∀ b, ∑ a, q a b = μ b) (g : S → ℝ) :
    (∑ s, ∑ t, pushedFlow ρ F q s t*g t) = ∑ r, ρ r*∑ b, μ b*g (F r b) := by
  rw [pushedFlow_test]
  apply Finset.sum_congr rfl; intro r _
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro b _
  rw [← Finset.sum_mul,hcol]

lemma pushedFlow_energy (ρ : R → ℝ) (F : R → A → S) (q : A → A → ℝ)
    (f : S → ℝ) : localEnergy (pushedFlow ρ F q) f =
    ∑ r, ρ r*localEnergy q (fun a => f (F r a)) := by
  unfold localEnergy
  rw [pushedFlow_test]
  simp only [mul_div_assoc,Finset.sum_div]

end

section

open Finset

variable {I Ω : Type*} [Fintype I] [DecidableEq I] [Fintype Ω] [DecidableEq Ω]

variable (p : I → Ω → ℝ)

noncomputable def pairFlow (x y : I) (Q : PairCapacity p x y) : (I → Ω) → (I → Ω) → ℝ :=
  pushedFlow (density p) (replacePair x y) Q.q

omit [DecidableEq Ω] in
lemma slice_mean (hs : ∀ i, ∑ a, p i a = 1) (x y : I) (f : (I → Ω) → ℝ) :
    mean p (fun s => ∑ a : Ω × Ω, p x a.1*p y a.2*f (replacePair x y s a)) = mean p f := by
  have he (s : I → Ω) : (∑ a : Ω × Ω, p x a.1*p y a.2*f (replacePair x y s a)) =
      average p x (average p y f) s := by
    rw [Fintype.sum_prod_type]
    simp only [average_apply,Finset.mul_sum]
    apply Finset.sum_congr rfl; intro a _
    apply Finset.sum_congr rfl; intro b _
    unfold replacePair; ring
  simp_rw [he]
  rw [mean_average p hs,mean_average p hs]

lemma pairFlow_row (hs : ∀ i, ∑ a, p i a = 1) (x y : I) (Q : PairCapacity p x y) (s : I → Ω) :
    (∑ t, pairFlow p x y Q s t) = density p s := by
  have h := pushedFlow_row_test (density p) (replacePair x y) Q.q
    (fun a => p x a.1*p y a.2) Q.row (fun t => if t=s then 1 else 0)
  change (∑ r, ∑ t, pairFlow p x y Q r t*(if r=s then 1 else 0)) =
    mean p (fun r => ∑ a : Ω × Ω, p x a.1*p y a.2*(if replacePair x y r a=s then 1 else 0)) at h
  rw [slice_mean p hs x y (fun t => if t=s then 1 else 0)] at h
  simpa [mean,mul_ite,Finset.sum_ite_irrel] using h

lemma pairFlow_col (hs : ∀ i, ∑ a, p i a = 1) (x y : I) (Q : PairCapacity p x y) (t : I → Ω) :
    (∑ s, pairFlow p x y Q s t) = density p t := by
  have h := pushedFlow_col_test (density p) (replacePair x y) Q.q
    (fun a => p x a.1*p y a.2) Q.col (fun s => if s=t then 1 else 0)
  change (∑ r, ∑ s, pairFlow p x y Q r s*(if s=t then 1 else 0)) =
    mean p (fun r => ∑ a : Ω × Ω, p x a.1*p y a.2*(if replacePair x y r a=t then 1 else 0)) at h
  rw [slice_mean p hs x y (fun s => if s=t then 1 else 0)] at h
  simpa [mean,mul_ite] using h

lemma pairFlow_nonneg (hp : ∀ i a, 0 ≤ p i a) (x y : I) (Q : PairCapacity p x y) (s t : I → Ω) :
    0 ≤ pairFlow p x y Q s t := pushedFlow_nonneg _ _ _ (density_nonneg p hp) Q.nonneg s t

lemma pairFlow_energy (x y : I) (Q : PairCapacity p x y) (f : (I → Ω) → ℝ) :
    localEnergy (pairFlow p x y Q) f = pairEnergy p x y Q f :=
  pushedFlow_energy _ _ _ f

noncomputable def baseFlow (i : I) : (I → Ω) → (I → Ω) → ℝ :=
  pushedFlow (density p) (fun s a => Function.update s i a) (fun a b => p i a*p i b)

lemma baseFlow_nonneg (hp : ∀ i a, 0 ≤ p i a) (i : I) (s t : I → Ω) :
    0 ≤ baseFlow p i s t := pushedFlow_nonneg _ _ _ (density_nonneg p hp)
      (fun a b => mul_nonneg (hp i a) (hp i b)) s t

lemma baseFlow_row (hs : ∀ i, ∑ a, p i a = 1) (i : I) (s : I → Ω) :
    (∑ t, baseFlow p i s t) = density p s := by
  have h := pushedFlow_row_test (density p) (fun r a => Function.update r i a)
    (fun a b => p i a*p i b) (p i) (fun a => by rw [← Finset.mul_sum,hs, mul_one])
    (fun t => if t=s then 1 else 0)
  change (∑ r, ∑ t, baseFlow p i r t*(if r=s then 1 else 0)) =
    mean p (average p i (fun t => if t=s then 1 else 0)) at h
  rw [mean_average p hs] at h
  simpa [mean,mul_ite,Finset.sum_ite_irrel] using h

lemma baseFlow_col (hs : ∀ i, ∑ a, p i a = 1) (i : I) (t : I → Ω) :
    (∑ s, baseFlow p i s t) = density p t := by
  have h := pushedFlow_col_test (density p) (fun r a => Function.update r i a)
    (fun a b => p i a*p i b) (p i) (fun b => by rw [← Finset.sum_mul,hs, one_mul])
    (fun s => if s=t then 1 else 0)
  change (∑ r, ∑ s, baseFlow p i r s*(if s=t then 1 else 0)) =
    mean p (average p i (fun s => if s=t then 1 else 0)) at h
  rw [mean_average p hs] at h
  simpa [mean,mul_ite] using h

lemma baseFlow_energy (hs : ∀ i, ∑ a, p i a = 1) (i : I) (f : (I → Ω) → ℝ) :
    localEnergy (baseFlow p i) f = baseEnergy p i f := by
  rw [baseFlow,pushedFlow_energy]
  have he (s : I → Ω) : localEnergy (fun a b => p i a*p i b) (fun a => f (Function.update s i a)) =
      average p i (fun r => (f r-average p i f r)^2) s := by
    have h := FiniteVariance.variance_eq_pair (p i) (fun a => f (Function.update s i a)) (hs i)
    rw [Fintype.sum_prod_type] at h
    unfold localEnergy
    rw [← h]
    simp only [FiniteVariance.variance,average_apply,Function.update_idem]
  simp_rw [he]
  change mean p (average p i (fun r => (f r-average p i f r)^2)) = _
  rw [mean_average p hs]
  exact mean_square p (f-average p i f)




noncomputable def updateCount (guides : I → Finset I) (base : Finset I) : ℕ :=
  (∑ x, (guides x).card)+base.card

noncomputable def scanFlow (guides : I → Finset I) (base : Finset I)
    (Q : ∀ x y, PairCapacity p x y) (s t : I → Ω) : ℝ :=
  (if s=t then density p s else 0)/2+
    ((∑ x, ∑ y ∈ guides x, pairFlow p x y (Q x y) s t)+
      ∑ i ∈ base, baseFlow p i s t)/(2*(updateCount guides base:ℝ))

end

section

open Finset

variable {Ω J : Type*} [Fintype Ω]

lemma localEnergy_add (q r : Ω → Ω → ℝ) (f : Ω → ℝ) :
    localEnergy (fun a b => q a b+r a b) f = localEnergy q f+localEnergy r f := by
  simp only [localEnergy,add_mul,Finset.sum_add_distrib,add_div]

lemma localEnergy_div (q : Ω → Ω → ℝ) (c : ℝ) (f : Ω → ℝ) :
    localEnergy (fun a b => q a b/c) f = localEnergy q f/c := by
  simp only [localEnergy,div_mul_eq_mul_div,← Finset.sum_div]
  ring

lemma localEnergy_sum (s : Finset J) (q : J → Ω → Ω → ℝ) (f : Ω → ℝ) :
    localEnergy (fun a b => ∑ i ∈ s, q i a b) f = ∑ i ∈ s, localEnergy (q i) f := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [localEnergy]
  | @insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    rw [localEnergy_add,ih]

lemma localEnergy_diag [DecidableEq Ω] (π : Ω → ℝ) (f : Ω → ℝ) :
    localEnergy (fun a b => if a=b then π a else 0) f = 0 := by
  unfold localEnergy
  have h (a b : Ω) : (if a=b then π a else 0)*(f a-f b)^2 = 0 := by
    by_cases hh : a=b <;> simp [hh]
  simp_rw [h]; simp

end

open Finset

variable {I Ω : Type*} [Fintype I] [DecidableEq I] [Fintype Ω] [DecidableEq Ω]

variable (p : I → Ω → ℝ)

omit [DecidableEq I] in
lemma updateCount_pos (guides : I → Finset I) (base : Finset I) (hb : base.Nonempty) :
    0 < updateCount guides base := Nat.add_pos_right _ (Finset.card_pos.mpr hb)

lemma scanFlow_nonneg (hp : ∀ i a, 0 ≤ p i a) (guides : I → Finset I) (base : Finset I)
    (Q : ∀ x y, PairCapacity p x y) (s t : I → Ω) : 0 ≤ scanFlow p guides base Q s t := by
  unfold scanFlow
  apply add_nonneg
  · apply div_nonneg _ (by norm_num)
    split_ifs <;> [exact density_nonneg p hp s; exact le_refl _]
  · apply div_nonneg _ (by positivity)
    exact add_nonneg (Finset.sum_nonneg (fun x _ => Finset.sum_nonneg
      (fun y _ => pairFlow_nonneg p hp x y (Q x y) s t)))
      (Finset.sum_nonneg (fun i _ => baseFlow_nonneg p hp i s t))

lemma scanFlow_lazy (hp : ∀ i a, 0 ≤ p i a) (guides : I → Finset I) (base : Finset I)
    (Q : ∀ x y, PairCapacity p x y) (s : I → Ω) : density p s/2 ≤ scanFlow p guides base Q s s := by
  unfold scanFlow
  simp only [ite_true,le_add_iff_nonneg_right]
  apply div_nonneg _ (by positivity)
  exact add_nonneg (Finset.sum_nonneg (fun x _ => Finset.sum_nonneg
      (fun y _ => pairFlow_nonneg p hp x y (Q x y) s s)))
    (Finset.sum_nonneg (fun i _ => baseFlow_nonneg p hp i s s))

lemma scanFlow_row (hs : ∀ i, ∑ a, p i a = 1) (guides : I → Finset I) (base : Finset I)
    (hb : base.Nonempty) (Q : ∀ x y, PairCapacity p x y) (s : I → Ω) :
    (∑ t, scanFlow p guides base Q s t) = density p s := by
  have hm : (updateCount guides base:ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt (updateCount_pos guides base hb))
  unfold scanFlow
  rw [Finset.sum_add_distrib,← Finset.sum_div,← Finset.sum_div]
  simp only [Finset.sum_ite_eq,Finset.mem_univ,ite_true]
  rw [Finset.sum_add_distrib,Finset.sum_comm]
  simp_rw [Finset.sum_comm (s := Finset.univ) (t := guides _)]
  simp_rw [pairFlow_row p hs]
  rw [Finset.sum_comm]
  simp only [baseFlow_row p hs,Finset.sum_const,nsmul_eq_mul]
  simp only [← Finset.sum_mul]
  have hc : (∑ x, ((guides x).card:ℝ))+(base.card:ℝ) = (updateCount guides base:ℝ) := by
    simp [updateCount,Nat.cast_sum]
  rw [← add_mul,hc]
  field_simp
  ring

lemma scanFlow_col (hs : ∀ i, ∑ a, p i a = 1) (guides : I → Finset I) (base : Finset I)
    (hb : base.Nonempty) (Q : ∀ x y, PairCapacity p x y) (t : I → Ω) :
    (∑ s, scanFlow p guides base Q s t) = density p t := by
  have hm : (updateCount guides base:ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt (updateCount_pos guides base hb))
  unfold scanFlow
  rw [Finset.sum_add_distrib,← Finset.sum_div,← Finset.sum_div]
  simp only [Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  rw [Finset.sum_add_distrib,Finset.sum_comm]
  simp_rw [Finset.sum_comm (s := Finset.univ) (t := guides _)]
  simp_rw [pairFlow_col p hs]
  rw [Finset.sum_comm]
  simp only [baseFlow_col p hs,Finset.sum_const,nsmul_eq_mul]
  simp only [← Finset.sum_mul]
  have hc : (∑ x, ((guides x).card:ℝ))+(base.card:ℝ) = (updateCount guides base:ℝ) := by
    simp [updateCount,Nat.cast_sum]
  rw [← add_mul,hc]
  field_simp
  ring

lemma scanFlow_energy (hs : ∀ i, ∑ a, p i a = 1) (guides : I → Finset I) (base : Finset I)
    (Q : ∀ x y, PairCapacity p x y) (f : (I → Ω) → ℝ) :
    localEnergy (scanFlow p guides base Q) f = scanEnergy p guides base Q f := by
  unfold scanFlow
  rw [localEnergy_add,localEnergy_div,localEnergy_diag,zero_div,zero_add,
    localEnergy_div,localEnergy_add]
  simp_rw [localEnergy_sum,pairFlow_energy,baseFlow_energy p hs]
  rfl

end MatchingFPRAS.Replica

namespace MatchingFPRAS.FiniteChain

open Finset MatchingFPRAS.Replica

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

noncomputable def sqNorm (π f : Ω → ℝ) : ℝ := ∑ a, π a*(f a)^2

noncomputable def massMean (π f : Ω → ℝ) : ℝ := ∑ a, π a*f a

noncomputable def stepDensity (π : Ω → ℝ) (C : Ω → Ω → ℝ) (f : Ω → ℝ) (b : Ω) : ℝ :=
  (∑ a, C a b*f a)/π b

omit [DecidableEq Ω] in
lemma stepDensity_mean (π : Ω → ℝ) (hp : ∀ a, 0 < π a) (C : Ω → Ω → ℝ)
    (hrow : ∀ a, ∑ b, C a b = π a) (f : Ω → ℝ) :
    massMean π (stepDensity π C f) = massMean π f := by
  unfold massMean stepDensity
  simp only [mul_div_cancel₀ _ (ne_of_gt (hp _))]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_mul,hrow]

omit [DecidableEq Ω] in
lemma stepDensity_one (π : Ω → ℝ) (hp : ∀ a, 0 < π a) (C : Ω → Ω → ℝ)
    (hcol : ∀ b, ∑ a, C a b = π b) : stepDensity π C (fun _ => 1) = (fun _ => 1) := by
  funext b; simp only [stepDensity,mul_one,hcol,div_self (ne_of_gt (hp b))]

omit [DecidableEq Ω] in
lemma stepDensity_linear (π : Ω → ℝ) (C : Ω → Ω → ℝ) (f g : Ω → ℝ) (c d : ℝ) :
    stepDensity π C (fun a => c*f a+d*g a) =
      fun b => c*stepDensity π C f b+d*stepDensity π C g b := by
  funext b
  have hc (a : Ω) : C a b*(c*f a) = c*(C a b*f a) := by ring
  have hd (a : Ω) : C a b*(d*g a) = d*(C a b*g a) := by ring
  simp only [stepDensity,mul_add,Finset.sum_add_distrib,hc,hd,← Finset.mul_sum,
    add_div,mul_div_assoc]

omit [DecidableEq Ω] in
lemma stepDensity_jensen (π : Ω → ℝ) (hp : ∀ a, 0 < π a) (C : Ω → Ω → ℝ)
    (hC : ∀ a b, 0 ≤ C a b) (hrow : ∀ a, ∑ b, C a b = π a)
    (hcol : ∀ b, ∑ a, C a b = π b) (f : Ω → ℝ) :
    sqNorm π (stepDensity π C f) ≤ sqNorm π f := by
  have h (b : Ω) : π b*(stepDensity π C f b)^2 ≤ ∑ a, C a b*(f a)^2 := by
    have hh := square_average (fun a => C a b/π b) (fun a => div_nonneg (hC a b) (hp b).le)
      (by rw [← Finset.sum_div,hcol,div_self (ne_of_gt (hp b))]) f
    have he : (∑ a, (C a b/π b)*f a) = stepDensity π C f b := by
      simp only [stepDensity,div_mul_eq_mul_div,Finset.sum_div]
    rw [he] at hh
    have hh := mul_le_mul_of_nonneg_left hh (hp b).le
    simp only [div_mul_eq_mul_div,← Finset.sum_div,mul_div_cancel₀ _ (ne_of_gt (hp b))] at hh
    exact hh
  have hh := Finset.sum_le_sum (fun b (_ : b ∈ Finset.univ) => h b)
  rw [Finset.sum_comm] at hh
  simp_rw [← Finset.sum_mul,hrow] at hh
  exact hh

omit [DecidableEq Ω] in
lemma energy_norm_cross (π : Ω → ℝ) (C : Ω → Ω → ℝ)
    (hrow : ∀ a, ∑ b, C a b = π a) (hcol : ∀ b, ∑ a, C a b = π b)
    (f : Ω → ℝ) : localEnergy C f = sqNorm π f-(∑ a, ∑ b, C a b*f a*f b) := by
  have he (a b : Ω) : C a b*(f a-f b)^2 = C a b*(f a)^2+C a b*(f b)^2-2*(C a b*f a*f b) := by ring
  unfold localEnergy
  simp_rw [he,Finset.sum_sub_distrib,Finset.sum_add_distrib]
  have hl : (∑ a, ∑ b, C a b*(f a)^2) = sqNorm π f := by
    simp_rw [← Finset.sum_mul,hrow]; rfl
  have hr : (∑ a, ∑ b, C a b*(f b)^2) = sqNorm π f := by
    rw [Finset.sum_comm]; simp_rw [← Finset.sum_mul,hcol]; rfl
  simp_rw [← Finset.mul_sum]
  rw [hl,hr]; ring

noncomputable def unlazyFlow (π : Ω → ℝ) (C : Ω → Ω → ℝ) (a b : Ω) : ℝ :=
  2*C a b-(if a=b then π a else 0)

omit [Fintype Ω] in
lemma unlazyFlow_nonneg (π : Ω → ℝ) (C : Ω → Ω → ℝ)
    (hC : ∀ a b, 0 ≤ C a b) (hlazy : ∀ a, π a/2 ≤ C a a) :
    ∀ a b, 0 ≤ unlazyFlow π C a b := by
  intro a b; unfold unlazyFlow
  by_cases h : a=b
  · subst b; simp only [ite_true]; linarith [hlazy a]
  · simp only [ite_eq_right h,sub_zero]; exact mul_nonneg (by norm_num) (hC a b)

lemma unlazyFlow_row (π : Ω → ℝ) (C : Ω → Ω → ℝ) (hrow : ∀ a, ∑ b, C a b = π a) (a : Ω) :
    (∑ b, unlazyFlow π C a b) = π a := by
  simp only [unlazyFlow,Finset.sum_sub_distrib,← Finset.mul_sum,hrow,
    Finset.sum_ite_eq,Finset.mem_univ,ite_true]
  ring

lemma unlazyFlow_col (π : Ω → ℝ) (C : Ω → Ω → ℝ) (hcol : ∀ b, ∑ a, C a b = π b) (b : Ω) :
    (∑ a, unlazyFlow π C a b) = π b := by
  simp only [unlazyFlow,Finset.sum_sub_distrib,← Finset.mul_sum,hcol,
    Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  ring

lemma unlazyFlow_step (π : Ω → ℝ) (hp : ∀ a, 0 < π a) (C : Ω → Ω → ℝ) (f : Ω → ℝ) :
    stepDensity π (unlazyFlow π C) f = fun b => 2*stepDensity π C f b-f b := by
  funext b
  simp only [stepDensity,unlazyFlow,sub_mul,Finset.sum_sub_distrib,ite_mul,zero_mul,
    Finset.sum_ite_eq',Finset.mem_univ,ite_true,sub_div,
    mul_div_cancel_left₀ (f b) (ne_of_gt (hp b))]
  simp_rw [mul_assoc,← Finset.mul_sum]
  ring

lemma lazy_l2 (π : Ω → ℝ) (hp : ∀ a, 0 < π a) (C : Ω → Ω → ℝ)
    (hC : ∀ a b, 0 ≤ C a b) (hrow : ∀ a, ∑ b, C a b = π a)
    (hcol : ∀ b, ∑ a, C a b = π b) (hlazy : ∀ a, π a/2 ≤ C a a)
    (f : Ω → ℝ) : sqNorm π (stepDensity π C f) ≤ sqNorm π f-localEnergy C f := by
  have hj := stepDensity_jensen π hp (unlazyFlow π C) (unlazyFlow_nonneg π C hC hlazy)
    (unlazyFlow_row π C hrow) (unlazyFlow_col π C hcol) f
  rw [unlazyFlow_step π hp] at hj
  have he : sqNorm π (fun b => 2*stepDensity π C f b-f b) =
      4*sqNorm π (stepDensity π C f)-4*(∑ a, ∑ b, C a b*f a*f b)+sqNorm π f := by
    have ht (b : Ω) : π b*(2*stepDensity π C f b-f b)^2 =
        4*(π b*(stepDensity π C f b)^2)-4*(π b*stepDensity π C f b*f b)+π b*(f b)^2 := by ring
    unfold sqNorm
    simp_rw [ht,Finset.sum_add_distrib,Finset.sum_sub_distrib,← Finset.mul_sum]
    congr 2
    simp only [stepDensity,mul_div_cancel₀ _ (ne_of_gt (hp _)),Finset.sum_mul]
    rw [Finset.sum_comm]
  rw [he] at hj
  rw [energy_norm_cross π C hrow hcol]
  linarith

end MatchingFPRAS.FiniteChain

end OAI
