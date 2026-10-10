import Mathlib
import OAI.Combinatorics.RamseyFive.Entropy.UniformHistory
import OAI.Combinatorics.RamseyFive.Trees.Windows
import OAI.Combinatorics.RamseyFive.Entropy.CollisionSampling

namespace OAI

noncomputable section

namespace SharpRamseyFive.FiniteEntropy

section
open scoped Classical BigOperators
variable {B A T β κ : Type} [Fintype B] [Fintype A] [Fintype T] [Fintype β]
  [Fintype κ] [Nonempty A]
local instance preRoundDeletionIndexDecEq : DecidableEq ((B×A)⊕T) := Classical.decEq _

def preRoundBad (_μ : Law κ) (p : κ→Law (((B×A)⊕T)→β))
    (_S : κ→B→Finset A) (n : ℕ) (J d e : ℝ)
    (c : κ→BlockHistory B A T β n→((B×A)⊕T)→((B×A)⊕T)→ℝ)
    (z : (κ×BlockHistory B A T β n)×(B→A)) (i : ((B×A)⊕T)) : ℝ :=
  indexBad J d e (historyPosterior (p z.1.1) z.1.2) (c z.1.1 z.1.2) z.2 i

theorem preRound_bad_budget (μ : Law κ) (p : κ→Law (((B×A)⊕T)→β))
    (S : κ→B→Finset A) (n r : ℕ) (hr : 0<r)
    (hS : ∀ c,0<μ c→∀ b,r+n≤(S c b).card)
    (J d e : ℝ) (hd : 0<d) (he : 0<e) (D : κ→((B×A)⊕T)→Finset β)
    (hJ : ∀ c i,Real.log (D c i).card≤J)
    (hp : ∀ c,0<μ c→InDomains (p c) (D c))
    (hfix : ∀ c,0<μ c→FixedOutside (p c) (blockActive (S c)))
    (c : κ→BlockHistory B A T β n→((B×A)⊕T)→((B×A)⊕T)→ℝ)
    (hc : ∀ a h i j,0≤c a h i j) (C : ℝ)
    (hC : ∀ a,0<μ a→∀ h,0<historyLaw (p a) (S a) n h→
      (∑ i∈blockActive (historyUnused (S a) h),
        ∑ j∈blockActive (historyUnused (S a) h),c a h i j)≤C) :
    mean (preRoundLaw μ p S n) (fun z=>∑ i∈blockActive (historyUnused (S z.1.1) z.1.2),
      preRoundBad μ p S n J d e c z i)≤
      mean μ (fun a=>activeDeficit (p a) (blockActive (S a)) J)/d+
      (mean (preRoundLaw μ p S n) (fun z=>blockAllInformation
        (historyPosterior (p z.1.1) z.1.2) (historyUnused (S z.1.1) z.1.2) z.2)+C/r)/e := by
  have hlocal (a : κ) (ha : 0<μ a) (h : BlockHistory B A T β n)
      (hh : 0<historyLaw (p a) (S a) n h) :
      mean (freshBlockLaw (historyUnused (S a) h))
        (fun s=>∑ i∈blockActive (historyUnused (S a) h),
          indexBad J d e (historyPosterior (p a) h) (c a h) s i)≤
        mean (freshBlockLaw (historyUnused (S a) h))
          (blockAllDeficit J (historyPosterior (p a) h) (historyUnused (S a) h))/d+
        (mean (freshBlockLaw (historyUnused (S a) h))
          (blockAllInformation (historyPosterior (p a) h) (historyUnused (S a) h))+C/r)/e := by
    apply (fresh_bad_bound J d e hd he _ ((history_in_domains (p a) (D a) (hp a ha) n h).entropy_cap J (hJ a))
      _ (hc a h) _ r hr (history_unused_card (S a) r n (hS a ha) h)).trans
    gcongr
    exact hC a ha h hh
  have hb := mean_mono_pos μ (fun a ha=>mean_mono_pos (historyLaw (p a) (S a) n)
    (hlocal a ha))
  simp_rw [mean_add,mean_div,mean_add,mean_const] at hb
  have hdef := preRoundLaw_deficit μ p S J D hJ hp hfix n
    (fun a ha b=>by have := hS a ha b; omega)
  unfold preRoundLaw at hdef ⊢
  simp only [mean_adaptive,preRoundBad] at hdef ⊢
  exact hb.trans (by gcongr)

theorem preRound_selected_bad (μ : Law κ) (p : κ→Law (((B×A)⊕T)→β))
    (S : κ→B→Finset A) (n r : ℕ) (hr : 0<r)
    (hS : ∀ a,0<μ a→∀ b,r+n≤(S a b).card)
    (J d e : ℝ)
    (c : κ→BlockHistory B A T β n→((B×A)⊕T)→((B×A)⊕T)→ℝ) :
    r*mean (preRoundLaw μ p S n) (fun z=>∑ b,preRoundBad μ p S n J d e c z
      (Sum.inl (b,z.2 b)))≤
    mean (preRoundLaw μ p S n) (fun z=>∑ i∈blockActive (historyUnused (S z.1.1) z.1.2),
      preRoundBad μ p S n J d e c z i) := by
  simp only [preRoundLaw,mean_adaptive,preRoundBad]
  rw [←mean_smul]
  apply mean_mono_pos
  intro a ha
  rw [←mean_smul]
  exact mean_mono (historyLaw (p a) (S a) n) fun h=>
    selected_bad_fraction J d e _ _ _ r hr (history_unused_card (S a) r n (hS a ha) h)

end

open scoped Classical BigOperators
variable {Ω W T : Type*} [Fintype Ω] [Fintype W] [Fintype T]

lemma badIndexIndicator_zero_or_one (δ g d e : ℝ) :
    badIndexIndicator δ g d e=0 ∨ badIndexIndicator δ g d e=1 := by
  unfold badIndexIndicator
  split_ifs <;> simp

theorem exists_good_window_pair (p : Law Ω) (a : Ω→W→T→ℝ) (b : Ω→W→ℝ)
    (ha : ∀ z v t,a z v t=0 ∨ a z v t=1)
    (hb : ∀ z v,b z v=0 ∨ b z v=1)
    (hsmall : mean p (fun z=>∑ v,∑ t,a z v t)+Fintype.card T*
      mean p (fun z=>∑ v,b z v)<(Fintype.card W:ℝ)*Fintype.card T) :
    ∃ z,0< p z ∧ ∃ v t,a z v t=0 ∧ b z v=0 := by
  by_contra hn
  push Not at hn
  have hp (z : Ω) (hz : 0< p z) :
      (Fintype.card W:ℝ)*Fintype.card T ≤
        (∑ v,∑ t,a z v t)+(Fintype.card T:ℝ)*∑ v,b z v := by
    have hpoint (v : W) (t : T) : 1≤ a z v t+b z v := by
      rcases ha z v t with h|h <;> rcases hb z v with h'|h'
      · exact False.elim (hn z hz v t h h')
      all_goals rw [h,h']; norm_num
    have H := Finset.sum_le_sum (s:=(Finset.univ:Finset W))
      (fun v _=> Finset.sum_le_sum (s:=(Finset.univ:Finset T)) (fun t _=> hpoint v t))
    simpa only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,
      nsmul_eq_mul,mul_one,←Finset.mul_sum] using H
  have H:= mean_mono_pos p hp
  rw [mean_const,mean_add,mean_smul] at H
  linarith

variable {κ β : Type} [Fintype κ] [Fintype β] {w r n rem : ℕ}
  [Nonempty (Fin r)]
local instance goodWindowBlockDecEq : DecidableEq (Fin w×Bool) := Classical.decEq _
local instance goodWindowIndexDecEq : DecidableEq (SharpRamseyFive.Windows.Slots w r) := Classical.decEq _

theorem preRound_good_early_middle (μ : Law κ)
    (p : κ→Law (SharpRamseyFive.Windows.Slots w r→β))
    (S : κ→(Fin w×Bool)→Finset (Fin r)) (hrem : 0< rem) (hr : r≤2*rem)
    (hS : ∀ a,0<μ a→∀ b,rem+n≤(S a b).card)
    (J d e : ℝ)
    (c : κ→BlockHistory (Fin w×Bool) (Fin r) (Fin w×Fin (2*r)) β n→
      SharpRamseyFive.Windows.Slots w r→SharpRamseyFive.Windows.Slots w r→ℝ)
    (hsmall : 5*mean (preRoundLaw μ p S n) (fun z=>
      ∑ i∈blockActive (historyUnused (S z.1.1) z.1.2),preRoundBad μ p S n J d e c z i)<2*r*w) :
    ∃ z,0< preRoundLaw μ p S n z ∧ ∃ v t,
      preRoundBad μ p S n J d e c z (Sum.inr (v,t))=0 ∧
      preRoundBad μ p S n J d e c z (Sum.inl ((v,false),z.2 (v,false)))=0 := by
  let ν:= preRoundLaw μ p S n
  let bad:= preRoundBad μ p S n J d e c
  let all:= fun z=>∑ i∈blockActive (historyUnused (S z.1.1) z.1.2),bad z i
  let selected:= fun z=>∑ b,bad z (Sum.inl (b,z.2 b))
  have hnon (z : (κ×BlockHistory (Fin w×Bool) (Fin r) (Fin w×Fin (2*r)) β n)×
      ((Fin w×Bool)→Fin r)) (i : SharpRamseyFive.Windows.Slots w r) : 0≤ bad z i :=
    badIndexIndicator_nonneg ..
  have hmid : mean ν (fun z=>∑ v,∑ t,bad z (Sum.inr (v,t)))≤ mean ν all := by
    apply mean_mono
    intro z
    dsimp only [all]
    rw [blockActive_sum]
    conv_rhs => arg 2; rw [Fintype.sum_prod_type]
    exact le_add_of_nonneg_left (Finset.sum_nonneg fun b _=> Finset.sum_nonneg fun a _=> hnon z _)
  have hearly : mean ν (fun z=>∑ v,bad z (Sum.inl ((v,false),z.2 (v,false))))≤ mean ν selected := by
    apply mean_mono
    intro z
    dsimp only [selected]
    rw [Fintype.sum_prod_type]
    apply Finset.sum_le_sum
    intro v _
    exact Finset.single_le_sum (f:=fun b=>bad z (Sum.inl ((v,b),z.2 (v,b)))) (fun b _=>hnon z _) (Finset.mem_univ false)
  have hsel : (rem:ℝ)*mean ν selected≤ mean ν all := preRound_selected_bad μ p S n rem hrem hS J d e c
  have hsel0 : 0≤ mean ν selected := mean_nonneg _ _ (fun z=> Finset.sum_nonneg fun b _=> hnon z _)
  have hr' : (2*r:ℕ)≤4*rem := by omega
  have hx : (2*r:ℝ)*mean ν (fun z=>∑ v,bad z (Sum.inl ((v,false),z.2 (v,false))))≤4*mean ν all := by
    have h:= mul_le_mul_of_nonneg_left hearly (show (0:ℝ)≤2*r by positivity)
    have hr'' : (2*r:ℝ)≤4*rem := by exact_mod_cast hr'
    nlinarith [mul_le_mul_of_nonneg_right hr'' hsel0]
  apply exists_good_window_pair ν (fun z v t=> bad z (Sum.inr (v,t)))
    (fun z v=> bad z (Sum.inl ((v,false),z.2 (v,false))))
  · intro z v t
    exact badIndexIndicator_zero_or_one ..
  · intro z v
    exact badIndexIndicator_zero_or_one ..
  · simpa only [Fintype.card_fin,Nat.cast_mul,Nat.cast_ofNat] using
      (show mean ν (fun z=>∑ v,∑ t,bad z (Sum.inr (v,t)))+(2*r:ℝ)*
        mean ν (fun z=>∑ v,bad z (Sum.inl ((v,false),z.2 (v,false))))<(w:ℝ)*(2*r) by
          dsimp only [ν,all,bad] at hmid hx ⊢
          nlinarith)
end SharpRamseyFive.FiniteEntropy

end

end OAI
