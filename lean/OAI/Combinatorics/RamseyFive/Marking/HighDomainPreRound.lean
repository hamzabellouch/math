import Mathlib
import OAI.Combinatorics.RamseyFive.Marking.HighFourPreRound
import OAI.Combinatorics.RamseyFive.Marking.HighDomainEndpoints

namespace OAI

namespace SharpRamseyFive.Marking
open Module SharpRamseyFive.ProjectiveIncidence SharpRamseyFive.FiniteEntropy
open SharpRamseyFive.HighSamples SharpRamseyFive.Windows
open scoped Classical LinearAlgebra.Projectivization BigOperators
noncomputable section
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
  [Fintype (ℙ K (Dual K (Dual K V)))]
  [Nonempty (ℙ K V)] [Nonempty (ℙ K (Dual K V))]
  [Nonempty (ℙ K (Dual K (Dual K V)))] {N r : ℕ} [Nonempty (Fin r)]
local instance highDomainPreBlockDE : DecidableEq (Fin 1×Bool) := Classical.decEq _
local instance highDomainPreIndexDE : DecidableEq (Slots 1 r) := Classical.decEq _

omit [Fintype (ℙ K (Dual K (Dual K V)))]
  [Nonempty (ℙ K V)] [Nonempty (ℙ K (Dual K V))]
  [Nonempty (ℙ K (Dual K (Dual K V)))] in
theorem high_domain_preRound_omissions {κ : Type} [Fintype κ] {n rem : ℕ}
    (hdim : finrank K V=5)
    (μ : Law κ) (p : κ→Law (Slots 1 r→FlagPair K V))
    (D : κ→Slots 1 r→Finset (FlagPair K V))
    (hD : ∀a,0<μ a→InDomains (p a) (D a))
    (r' : ℕ) (hr' : r'≤4) (hcap : ∀a,0<μ a→∀i,HighCaps (D a i) 4 r')
    (hcons : ∀ a,0<μ a→∀ x,0<p a x→∀ i j,slotEmbedding i<slotEmbedding j→
      Incident (x i).1 (x j).2→Incident (x j).1 (x i).2)
    (hflag : ∀ a,0<μ a→∀ x,0<p a x→∀ i,Incident (x i).1 (x i).2)
    (S : κ→(Fin 1×Bool)→Finset (Fin r)) (hrem : 0<rem) (hr : r≤2*rem)
    (hS : ∀ a,0<μ a→∀ b,rem+n≤(S a b).card)
    (J d s ε : ℝ) (hJ : 4*Real.log (Nat.card K)≤J) (hs : 0<s) (hd : 0≤d) (he : 0≤ε)
    (hbad : highBadMass s d 153≤(1:ℝ)/4)
    (hsmall : 2*(Nat.card K:ℝ)^2*(2*Real.exp s/(Nat.card K:ℝ)^4)≤1/(20*(Nat.card K:ℝ)))
    (c : κ→BlockHistory (Fin 1×Bool) (Fin r) (Fin 1×Fin (2*r)) (FlagPair K V) n→
      Slots 1 r→Slots 1 r→ℝ)
    (hc : ∀ a z i j,0≤c a z i j) (hcs : ∀ a z i j,c a z i j=c a z j i)
    (h : ℕ) :
    mean (adaptiveLaw (preRoundTupleLaw μ p S n) (fun z=>highFourSampler p r' s h z.1))
      (fun z=>((coveredPositions (fun t=>z.1.2 (Sum.inr (0,t))) (highDomain z.2))ᶜ.card:ℝ))≤
      5*mean (preRoundLaw μ p S n) (fun z=>
        ∑ i∈blockActive (historyUnused (S z.1.1) z.1.2),preRoundBad μ p S n J d ε c z i)+
        (2*r:ℝ)*highFourLoss (Nat.card K) r' h s d ε := by
  refine preRound_ready_omissions μ p S hrem hr hS J d ε
    (highFourLoss (Nat.card K) r' h s d ε)
    (highFourLoss_nonneg _ (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt
      (Nat.zero_lt_of_lt (Finite.one_lt_card (α:=K))))) r' h s d ε hs hd he) c
    (highFourSampler p r' s h) highDomain ?_
  intro z hz t hrdy
  have ha:=(preRound_positive μ p S n z hz).1
  change _ ≤ highFourLoss (Nat.card K) r' h s d ε
  unfold highFourSampler highFourLoss
  apply high_domain_good_pair_loss hdim (D z.1.1)
    (historyPosterior (p z.1.1) z.1.2) _ r' hr' (hcap _ ha) _ _
    J d s ε hJ hs hbad hsmall (c z.1.1 z.1.2) (hc _ _) (hcs _ _)
    z.2 0 t hrdy h
  · intro i
    exact marginal_support_subset _ _ (history_in_domains _ _ (hD _ ha) n z.1.2) i
  · intro x hx i j hij hi
    exact hcons _ ha x (history_support (p z.1.1) n z.1.2 x hx) i j hij hi
  · intro x hx i
    exact hflag _ ha x (history_support (p z.1.1) n z.1.2 x hx) i
end
end SharpRamseyFive.Marking

end OAI
