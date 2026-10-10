import Mathlib
import OAI.Combinatorics.RamseyFive.Entropy.LogSum

namespace OAI

namespace SharpRamseyFive.FiniteEntropy

section
open scoped BigOperators Classical
variable {α β : Type*} [Fintype α] [Fintype β]

theorem entropy_le_cross_entropy (p : Law α) (q : α → ℝ)
    (hq : ∀ a,0≤q a) (hs : ∑ a,q a≤1) (hac : ∀ a,0<p a → 0<q a) :
    entropy p≤ -(∑ a,p a*Real.log (q a)) := by
  have hh:=Finset.sum_le_sum (fun a (_ : a∈Finset.univ) =>
    point_log_ratio (p a) (q a) (p.nonneg a) (hq a) (hac a))
  rw [Finset.sum_sub_distrib,p.sum_one] at hh
  have he (a : α) : p a*Real.log (p a/q a)=p a*Real.log (p a)-p a*Real.log (q a) := by
    by_cases hz : p a=0
    · simp [hz]
    · rw [Real.log_div hz (ne_of_gt (hac a (lt_of_le_of_ne (p.nonneg a) (Ne.symm hz)))),mul_sub]
  simp only [he,Finset.sum_sub_distrib] at hh
  unfold entropy
  linarith

theorem option_entropy_bound (p : Law (Option β)) (S : Finset β) (N : ℝ)
    (hN : 1≤N) (hS : (S.card:ℝ)≤N)
    (hsupp : ∀ b,0<p (some b) → b∈S) :
    entropy p≤Real.log 2+(∑ b,p (some b))*Real.log N := by
  have hN0 : 0<N := zero_lt_one.trans_le hN
  let q : Option β → ℝ := fun o => match o with
    | none => 1/2
    | some b => if b∈S then 1/(2*N) else 0
  have hqsum : (∑ o,q o)=1/2+(S.card:ℝ)/(2*N) := by
    simp only [Fintype.sum_option,q]
    simp [div_eq_mul_inv]
  have hqnon (o : Option β) : 0≤q o := by
    cases o with
    | none => norm_num [q]
    | some b => simp only [q]; split_ifs <;> positivity
  have hqsumle : ∑ o,q o≤1 := by
    rw [hqsum]
    have hh : (S.card:ℝ)/(2*N)≤1/2 := by
      apply (div_le_iff₀ (by positivity)).mpr
      nlinarith
    linarith
  have hac (o : Option β) (ho : 0<p o) : 0<q o := by
    cases o with
    | none => norm_num [q]
    | some b => simp only [q,ite_eq_left (hsupp b ho)]; positivity
  have hb:=entropy_le_cross_entropy p q hqnon hqsumle hac
  have hlog : Real.log (1/(2*N))= -Real.log 2-Real.log N := by
    rw [Real.log_div (by norm_num) (by positivity),Real.log_one,
      Real.log_mul (by norm_num) (ne_of_gt hN0)]
    ring
  have hsome (b : β) : p (some b)*Real.log (q (some b))=
      p (some b)*(-Real.log 2-Real.log N) := by
    by_cases hz : p (some b)=0
    · simp only [hz,zero_mul]
    · rw [show q (some b)=1/(2*N) by
        exact ite_eq_left (hsupp b (lt_of_le_of_ne (p.nonneg _) (Ne.symm hz))),hlog]
  have hnone : Real.log (q none)= -Real.log 2 := by
    change Real.log (1/2)=_
    rw [Real.log_div (by norm_num) (by norm_num),Real.log_one,zero_sub]
  simp only [Fintype.sum_option,hsome,hnone,←Finset.sum_mul] at hb
  have hsum : p none+∑ b,p (some b)=1 := by simpa only [Fintype.sum_option] using p.sum_one
  have hsumlog := congrArg (fun x : ℝ => x*Real.log 2) hsum
  nlinarith

end

section
open scoped BigOperators Classical
variable {α β ι μ : Type*} [Fintype α] [Fintype β] [Fintype ι] [Fintype μ]

noncomputable def present (o : Option β) : ℝ := match o with
  | none => 0 | some _ => 1

lemma present_sum (p : Law α) (f : α → Option β) :
    (∑ b,map p f (some b))=∑ a,p a*present (f a) := by
  rw [←sum_map p f present]
  simp only [Fintype.sum_option,present,mul_zero,mul_one,zero_add]

theorem marked_entropy (p : Law α) (f : α → ι → Option β)
    (S : ι → Finset β) (N : ℝ) (hN : 1≤N) (hS : ∀ i,(S i).card≤N)
    (hsupp : ∀ a,0<p a → ∀ i b,f a i=some b → b∈S i) :
    entropy (map p f)≤(Fintype.card ι:ℝ)*Real.log 2+
      (∑ a,p a*(∑ i,present (f a i)))*Real.log N := by
  have hi (i : ι) : entropy (map p (fun a => f a i))≤Real.log 2+
      (∑ a,p a*present (f a i))*Real.log N := by
    rw [←present_sum p (fun a => f a i)]
    apply option_entropy_bound _ (S i) N hN (hS i)
    intro b hb
    by_contra hnot
    have hz : map p (fun a => f a i) (some b)=0 := by
      apply Finset.sum_eq_zero
      intro a _
      split_ifs with he
      · exact le_antisymm (le_of_not_gt (fun hpos => hnot (hsupp a hpos i b he))) (p.nonneg a)
      · rfl
    linarith
  have hc:=totalCorrelation_nonneg (map p f)
  simp only [totalCorrelation,map_comp,Function.comp_def] at hc
  have hh:=Finset.sum_le_sum (fun i (_ : i∈Finset.univ) => hi i)
  simp only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,
    ←Finset.sum_mul] at hh
  rw [Finset.sum_comm (f := fun i a => p a*present (f a i))] at hh
  simp only [←Finset.mul_sum] at hh
  linarith

theorem marked_mask_entropy (p : Law α) (mask : α → μ) (f : α → ι → Option β)
    (S : ι → Finset β) (N : ℝ) (hN : 1≤N) (hS : ∀ i,(S i).card≤N)
    (hsupp : ∀ a,0<p a → ∀ i b,f a i=some b → b∈S i) :
    entropy (pair p mask f)≤Real.log (Fintype.card μ)+(Fintype.card ι:ℝ)*Real.log 2+
      (∑ a,p a*(∑ i,present (f a i)))*Real.log N := by
  have hh:=entropy_subadditive (pair p mask f)
  rw [first_pair,second_pair] at hh
  have hmask:=entropy_le_log_card (map p mask)
  have hf:=marked_entropy p f S N hN hS hsupp
  linarith

end

open scoped BigOperators Classical
variable {α β ι μ κ : Type*} [Fintype α] [Fintype β] [Fintype ι] [Fintype μ] [Fintype κ]

lemma sum_fiber (p : Law (κ × α)) (g : α → ℝ) :
    (∑ c,first p c*(∑ a,fiber p c a*g a))=∑ a,second p a*g a := by
  simp only [Finset.mul_sum,←mul_assoc,←mass_eq_first_mul_fiber]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  rw [←Finset.sum_mul]
  rfl

theorem conditional_marked_entropy (p : Law (κ × α))
    (mask : α → μ) (f : α → ι → Option β)
    (S : κ → ι → Finset β) (N : ℝ) (hN : 1≤N)
    (hS : ∀ c i,((S c i).card:ℝ)≤N)
    (hsupp : ∀ c a,0<p (c,a) → ∀ i b,f a i=some b → b∈S c i) :
    (∑ c,first p c*entropy (pair (fiber p c) mask f))≤
      Real.log (Fintype.card μ)+(Fintype.card ι:ℝ)*Real.log 2+
        (∑ a,second p a*(∑ i,present (f a i)))*Real.log N := by
  have hh (c : κ) : first p c*entropy (pair (fiber p c) mask f)≤
      first p c*(Real.log (Fintype.card μ)+(Fintype.card ι:ℝ)*Real.log 2+
        (∑ a,fiber p c a*(∑ i,present (f a i)))*Real.log N) := by
    by_cases hc : first p c=0
    · simp only [hc,zero_mul,le_refl]
    · apply mul_le_mul_of_nonneg_left _ ((first p).nonneg c)
      apply marked_mask_entropy _ mask f (S c) N hN (hS c)
      intro a ha i b he
      apply hsupp c a _ i b he
      rw [mass_eq_first_mul_fiber]
      exact mul_pos (lt_of_le_of_ne ((first p).nonneg c) (Ne.symm hc)) ha
  apply (Finset.sum_le_sum (fun c (_ : c∈Finset.univ) => hh c)).trans_eq
  simp only [mul_add,Finset.sum_add_distrib,←Finset.sum_mul]
  rw [(first p).sum_one,one_mul,one_mul]
  simp only [←mul_assoc]
  rw [←Finset.sum_mul,sum_fiber]

end SharpRamseyFive.FiniteEntropy

end OAI
