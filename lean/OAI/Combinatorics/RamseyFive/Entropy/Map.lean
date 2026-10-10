import Mathlib
import OAI.Combinatorics.RamseyFive.Entropy.Law

namespace OAI

namespace SharpRamseyFive.FiniteEntropy
open scoped BigOperators Classical
variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]

@[ext] lemma Law.ext {p q : Law α} (h : p.mass=q.mass) : p=q := by
  cases p
  cases q
  cases h
  rfl

noncomputable def map (p : Law α) (f : α → β) : Law β where
  mass b := ∑ a, if f a=b then p a else 0
  nonneg b := Finset.sum_nonneg fun a _ => by
    split_ifs
    · exact p.nonneg a
    · exact le_rfl
  sum_one := by
    rw [Finset.sum_comm]
    classical
    simpa using p.sum_one

lemma sum_map (p : Law α) (f : α → β) (w : β → ℝ) :
    (∑ b,map p f b*w b) = ∑ a,p a*w (f a) := by
  change (∑ b,(∑ a,if f a=b then p a else 0)*w b)=_
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  classical
  simp [ite_mul]

lemma map_id (p : Law α) : map p id = p := by
  apply Law.ext
  funext a
  classical
  simp [map]

lemma map_comp (p : Law α) (f : α → β) (g : β → γ) :
    map (map p f) g = map p (g ∘ f) := by
  apply Law.ext
  funext c
  change (∑ b,if g b=c then map p f b else 0)=_
  have h := sum_map p f (fun b => if g b=c then 1 else 0)
  simpa only [mul_ite,mul_one,mul_zero,map,Function.comp_apply] using h

lemma map_mass_image (p : Law α) (f : α → β) (hf : Function.Injective f) (a : α) :
    map p f (f a)=p a := by
  change (∑ b,if f b=f a then p b else 0)=_
  classical
  simp [hf.eq_iff]

lemma entropy_map_injective (p : Law α) (f : α → β) (hf : Function.Injective f) :
    entropy (map p f)=entropy p := by
  unfold entropy
  rw [sum_map]
  simp only [map_mass_image p f hf]

noncomputable def pair (p : Law α) (f : α → β) (g : α → γ) : Law (β × γ) :=
  map p (fun a => (f a,g a))

lemma first_pair (p : Law α) (f : α → β) (g : α → γ) : first (pair p f g)=map p f := by
  apply Law.ext
  funext b
  simp only [first,pair,map]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  by_cases h : f a=b
  · simp [h,Prod.mk.injEq]
  · simp [h,Prod.mk.injEq]

lemma second_pair (p : Law α) (f : α → β) (g : α → γ) : second (pair p f g)=map p g := by
  apply Law.ext
  funext c
  simp only [second,pair,map]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  by_cases h : g a=c
  · simp [h,Prod.mk.injEq]
  · simp [h,Prod.mk.injEq]

noncomputable def fiber (p : Law (α × β)) (a : α) : Law β :=
  if h : 0 < first p a then
    { mass := fun b => p (a,b)/first p a
      nonneg := fun b => div_nonneg (p.nonneg _) h.le
      sum_one := by rw [←Finset.sum_div]; exact div_self (ne_of_gt h) }
  else second p

lemma mass_eq_first_mul_fiber (p : Law (α × β)) (a : α) (b : β) :
    p (a,b)=first p a*fiber p a b := by
  by_cases h : 0 < first p a
  · simp only [fiber,dite_eq_left h]
    field_simp
  · have hz : first p a=0 := le_antisymm (le_of_not_gt h) ((first p).nonneg a)
    have hpz : p (a,b)=0 := le_antisymm ((le_first p a b).trans_eq hz) (p.nonneg _)
    simp only [hpz,hz,zero_mul]

lemma log_mass_split (p : Law (α × β)) (a : α) (b : β) :
    p (a,b)*Real.log (p (a,b)) =
      p (a,b)*Real.log (first p a)+
      first p a*(fiber p a b*Real.log (fiber p a b)) := by
  by_cases h : p (a,b)=0
  · rw [h,zero_mul,zero_mul,zero_add]
    have hprod := mass_eq_first_mul_fiber p a b
    rw [h] at hprod
    rw [←mul_assoc,←hprod,zero_mul]
  · have hp : 0 < p (a,b) := lt_of_le_of_ne (p.nonneg _) (Ne.symm h)
    have h1 : first p a ≠ 0 := ne_of_gt (hp.trans_le (le_first p a b))
    have h2 : fiber p a b ≠ 0 := by
      intro hz
      rw [mass_eq_first_mul_fiber p a b,hz,mul_zero] at h
      exact h rfl
    conv_lhs => rw [mass_eq_first_mul_fiber p a b,Real.log_mul h1 h2]
    rw [mass_eq_first_mul_fiber p a b]
    ring

theorem entropy_chain (p : Law (α × β)) :
    entropy p = entropy (first p)+∑ a,first p a*entropy (fiber p a) := by
  have hlog : (∑ a,∑ b,p (a,b)*Real.log (first p a)) =
      ∑ a,first p a*Real.log (first p a) := by
    apply Finset.sum_congr rfl
    intro a _
    rw [←Finset.sum_mul]
    rfl
  simp only [entropy,Fintype.sum_prod_type,log_mass_split,Finset.sum_add_distrib,
    hlog,←Finset.mul_sum,mul_neg,Finset.sum_neg_distrib]
  ring

lemma entropy_first_le (p : Law (α × β)) : entropy (first p) ≤ entropy p := by
  rw [entropy_chain]
  exact le_add_of_nonneg_right (Finset.sum_nonneg fun a _ =>
    mul_nonneg ((first p).nonneg _) (entropy_nonneg _))

lemma conditional_entropy_le (p : Law (α × β)) :
    (∑ a,first p a*entropy (fiber p a)) ≤ entropy (second p) := by
  have := entropy_subadditive p
  rw [entropy_chain] at this
  linarith

lemma entropy_map_le (p : Law α) (f : α → β) : entropy (map p f) ≤ entropy p := by
  have h := entropy_first_le (pair p f id)
  rw [first_pair] at h
  rw [pair,entropy_map_injective p (fun a => (f a,id a)) (by
    intro a b hab
    exact congrArg Prod.snd hab)] at h
  exact h

theorem conditional_deficit_le (p : Law (α × β)) (capA capB : ℝ)
    (hcap : entropy (first p) ≤ capA) :
    (∑ a,first p a*(capB-entropy (fiber p a))) ≤ capA+capB-entropy p := by
  have he : (∑ a,first p a*(capB-entropy (fiber p a))) =
      capB-∑ a,first p a*entropy (fiber p a) := by
    simp only [mul_sub,Finset.sum_sub_distrib,←Finset.sum_mul,(first p).sum_one,one_mul]
  rw [he,entropy_chain]
  linarith

end SharpRamseyFive.FiniteEntropy

end OAI
