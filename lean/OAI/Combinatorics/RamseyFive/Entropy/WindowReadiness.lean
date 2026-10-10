import Mathlib
import OAI.Combinatorics.RamseyFive.Entropy.PreRoundDeletion

namespace OAI

namespace SharpRamseyFive.FiniteEntropy
open SharpRamseyFive.Windows
open scoped Classical BigOperators
noncomputable section
variable {κ β : Type} [Fintype κ] [Fintype β] {w r n rem : ℕ} [Nonempty (Fin r)]
local instance readinessBlockDE : DecidableEq (Fin w×Bool) := Classical.decEq _
local instance readinessIndexDE : DecidableEq (Slots w r) := Classical.decEq _

def windowReady (bad : Slots w r→ℝ) (sel : (Fin w×Bool)→Fin r) (v : Fin w) (t : Fin (2*r)) : Prop :=
  bad (Sum.inr (v,t))=0 ∧ ∀ b : Bool,bad (Sum.inl ((v,b),sel (v,b)))=0

omit [Nonempty (Fin r)] in
lemma window_not_ready_le (bad : Slots w r→ℝ) (sel : (Fin w×Bool)→Fin r)
    (hb : ∀ i,bad i=0 ∨ bad i=1) (v : Fin w) (t : Fin (2*r)) :
    (if windowReady bad sel v t then (0:ℝ) else 1)≤
      bad (Sum.inr (v,t))+∑ b : Bool,bad (Sum.inl ((v,b),sel (v,b))) := by
  simp only [Fintype.sum_bool]
  rcases hb (Sum.inr (v,t)) with h|h <;>
    rcases hb (Sum.inl ((v,true),sel (v,true))) with he|he <;>
      rcases hb (Sum.inl ((v,false),sel (v,false))) with hl|hl
  all_goals (simp only [windowReady,Bool.forall_bool,h,he,hl]; norm_num)

theorem preRound_ready_loss (μ : Law κ) (p : κ→Law (Slots w r→β))
    (S : κ→(Fin w×Bool)→Finset (Fin r)) (hrem : 0<rem) (hr : r≤2*rem)
    (hS : ∀ a,0<μ a→∀ b,rem+n≤(S a b).card) (J d e : ℝ)
    (c : κ→BlockHistory (Fin w×Bool) (Fin r) (Fin w×Fin (2*r)) β n→Slots w r→Slots w r→ℝ) :
    mean (preRoundLaw μ p S n) (fun z=>∑ v,∑ t,
      if windowReady (preRoundBad μ p S n J d e c z) z.2 v t then (0:ℝ) else 1)≤
      5*mean (preRoundLaw μ p S n) (fun z=>
        ∑ i∈blockActive (historyUnused (S z.1.1) z.1.2),preRoundBad μ p S n J d e c z i) := by
  let ν:=preRoundLaw μ p S n
  let bad:=preRoundBad μ p S n J d e c
  let all:=fun z=>∑ i∈blockActive (historyUnused (S z.1.1) z.1.2),bad z i
  let selected:=fun z=>∑ b,bad z (Sum.inl (b,z.2 b))
  have hnon (z : (κ×BlockHistory (Fin w×Bool) (Fin r) (Fin w×Fin (2*r)) β n)×
      ((Fin w×Bool)→Fin r)) (i : Slots w r) : 0≤bad z i := badIndexIndicator_nonneg ..
  have hmid : mean ν (fun z=>∑ v,∑ t,bad z (Sum.inr (v,t)))≤ mean ν all := by
    apply mean_mono
    intro z
    dsimp only [all]
    rw [blockActive_sum]
    conv_rhs => arg 2; rw [Fintype.sum_prod_type]
    exact le_add_of_nonneg_left (Finset.sum_nonneg fun b _=>Finset.sum_nonneg fun a _=>hnon z _)
  have hsel : (rem:ℝ)*mean ν selected≤ mean ν all := preRound_selected_bad μ p S n rem hrem hS J d e c
  have hsel0 : 0≤ mean ν selected := mean_nonneg _ _ (fun z=>Finset.sum_nonneg fun b _=>hnon z _)
  have hr' : (2*r:ℝ)≤4*rem := by exact_mod_cast (show 2*r≤4*rem by omega)
  have hweight := mul_le_mul_of_nonneg_right hr' hsel0
  have hpoint : mean ν (fun z=>∑ v,∑ t,
      if windowReady (bad z) z.2 v t then (0:ℝ) else 1)≤
      mean ν (fun z=>∑ v,∑ t,bad z (Sum.inr (v,t)))+(2*r:ℝ)*mean ν selected := by
    have hh:=mean_mono ν (fun z=>Finset.sum_le_sum (s:=(Finset.univ:Finset (Fin w)))
      (fun v _=>Finset.sum_le_sum (s:=(Finset.univ:Finset (Fin (2*r))))
        (fun t _=>window_not_ready_le (bad z) z.2 (fun i=>badIndexIndicator_zero_or_one ..) v t)))
    simp only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,
      nsmul_eq_mul,Nat.cast_mul,Nat.cast_ofNat,←Finset.mul_sum,mean_add,mean_smul] at hh
    simpa only [selected,Fintype.sum_prod_type] using hh
  change mean ν (fun z=>∑ v,∑ t,if windowReady (bad z) z.2 v t then (0:ℝ) else 1)≤5*mean ν all
  linarith
end
end SharpRamseyFive.FiniteEntropy

end OAI
