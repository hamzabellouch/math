import Mathlib
import OAI.Combinatorics.RamseyFive.Entropy.GoodPairScores
import OAI.Combinatorics.RamseyFive.Entropy.WindowReadiness
import OAI.Combinatorics.RamseyFive.Marking.DomainTransport
import OAI.Combinatorics.RamseyFive.Marking.HighLowConflict
import OAI.Combinatorics.RamseyFive.Marking.HighSampleRetention

namespace OAI

namespace SharpRamseyFive.Marking

section
open Module ProjectiveIncidence FiniteEntropy HighSamples
open scoped Classical LinearAlgebra.Projectivization BigOperators
noncomputable section
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
local instance hdePDE : DecidableEq (ℙ K V) := Classical.decEq _
local instance hdeDDE : DecidableEq (ℙ K (Dual K V)) := Classical.decEq _

omit [FiniteDimensional K V] in
lemma HighCaps.endpoint_bad {D : Finset (FlagPair K V)} {r r' : ℕ}
    (h : HighCaps D r r') (p : Law (FlagPair K V)) (hD : support p⊆D)
    (hr : r≤4) (hr' : r'≤4) (s d : ℝ) (hs : 0<s)
    (hent : 4*Real.log (Nat.card K)-entropy p≤d) :
    eventMass (FiniteEntropy.first p) (highLeft p r' s)ᶜ≤highBadMass s d 153 ∧
      eventMass (FiniteEntropy.second p) (highRight p r s)ᶜ≤highBadMass s d 153 := by
  have hq : 0<(Nat.card K:ℝ) := by exact_mod_cast Nat.zero_lt_of_lt (Finite.one_lt_card (α:=K))
  constructor
  · exact high_endpoint_bad_of_domain p D hD (Nat.card K) s d 153 r' hq hs hr'
      h.first h.flag h.firstPartners hent
  · exact high_endpoint_bad_second_of_domain p D hD (Nat.card K) s d 153 r hq hs hr
      h.second h.flag h.secondPartners hent

omit [FiniteDimensional K V] in
lemma HighCaps.three_mass {D : Finset (FlagPair K V)} (h : HighCaps D 3 3)
    (p : Law (FlagPair K V)) (hD : support p⊆D) (s d : ℝ) (hs : 0<s)
    (hent : 4*Real.log (Nat.card K)-entropy p≤d) (hsmall : highBadMass s d 153≤(1:ℝ)/4) :
    (3:ℝ)/4≤eventMass (FiniteEntropy.first p) (highThreeLeft p s) ∧
      (3:ℝ)/4≤eventMass (FiniteEntropy.second p) (highThreeRight p s) := by
  have hb:=h.endpoint_bad p hD (by decide) (by decide) s d hs hent
  constructor
  · exact high_endpoint_mass p (Nat.card K) s d 153 3 hb.1 hsmall
  · have hcomp:=eventMass_complement (FiniteEntropy.second p) (highThreeRight p s)
    change eventMass (FiniteEntropy.first p) (highThreeLeft p s)ᶜ≤highBadMass s d 153 ∧
      eventMass (FiniteEntropy.second p) (highThreeRight p s)ᶜ≤highBadMass s d 153 at hb
    linarith [hb.2]

theorem high_domain_pair_loss (hdim : finrank K V=5)
    (D₁ D₂ : Finset (FlagPair K V)) (r' : ℕ) (hr' : r'≤4)
    (hcap₁ : HighCaps D₁ 4 r') (hcap₂ : HighCaps D₂ 4 r')
    (p : Law (FlagPair K V×FlagPair K V))
    (hD1 : support (FiniteEntropy.first p)⊆D₁) (hD2 : support (FiniteEntropy.second p)⊆D₂)
    (hcons : ∀ z,0<p z→Incident z.1.1 z.2.2→Incident z.2.1 z.1.2)
    (hflag : ∀ z,0<second p z→Incident z.1 z.2)
    (s d ε : ℝ) (hs : 0<s)
    (hent1 : 4*Real.log (Nat.card K)-entropy (FiniteEntropy.first p)≤d)
    (hent2 : 4*Real.log (Nat.card K)-entropy (FiniteEntropy.second p)≤d)
    (hbad : highBadMass s d 153≤(1:ℝ)/4)
    (hI : entropy (FiniteEntropy.first p)+entropy (FiniteEntropy.second p)-entropy p≤ε)
    (hsmall : 2*(Nat.card K:ℝ)^2*(2*Real.exp s/(Nat.card K:ℝ)^4)≤1/(20*(Nat.card K:ℝ)))
    (h : ℕ) :
    mean (FiniteEntropy.second p) (fun z=>eventWeight
      (iid (iid (highRepresentative (FiniteEntropy.first p) 4 r' s) (Fin h)) (Fin 3))
      (fun x=>z∉highDomain x))≤
      highBadMass s d 153+64*(Nat.card K:ℝ)^5*(2*Real.exp s/(Nat.card K:ℝ)^r')*
        (Real.exp s/(Nat.card K:ℝ)^4)+3*(1-1/(5*(Nat.card K:ℝ)))^h+12*h*ε := by
  have hB1:=hcap₁.endpoint_bad (FiniteEntropy.first p) hD1 (by decide) hr' s d hs hent1
  have hB2:=hcap₂.endpoint_bad (FiniteEntropy.second p) hD2 (by decide) hr' s d hs hent2
  have half:=high_pair_half (FiniteEntropy.first p) 4 r' s _ hB1.1 hB1.2 hbad
  have hrep:=highRepresentative_bounds (FiniteEntropy.first p) 4 r' s half
  have hconf:=highRepresentative_conflict p 4 r' s ε hcons half hI
  apply (sampled_target_loss hdim (highRepresentative (FiniteEntropy.first p) 4 r' s) (FiniteEntropy.second p) hflag
    (highRight (FiniteEntropy.second p) 4 s) (2*Real.exp s/(Nat.card K:ℝ)^r')
    (Real.exp s/(Nat.card K:ℝ)^4) (2*Real.exp s/(Nat.card K:ℝ)^4)
    (by positivity) (by positivity) (by positivity) hrep.2.1
    (highRight_cap (FiniteEntropy.second p) 4 s) hrep.2.2 hsmall h).trans
  have hmul:=mul_le_mul_of_nonneg_left hconf (show 0≤3*(h:ℝ) by positivity)
  linarith [hB2.2]
end
end

open Module SharpRamseyFive.ProjectiveIncidence SharpRamseyFive.FiniteEntropy
open SharpRamseyFive.HighSamples SharpRamseyFive.Windows
open scoped Classical LinearAlgebra.Projectivization BigOperators
noncomputable section
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
  [Fintype (ℙ K (Dual K (Dual K V)))]
  [Nonempty (ℙ K V)] [Nonempty (ℙ K (Dual K V))]
  [Nonempty (ℙ K (Dual K (Dual K V)))] {N w r : ℕ} [Nonempty (Fin r)]
local instance highDomainStageBlockDE : DecidableEq (Fin w×Bool) := Classical.decEq _
local instance highDomainStageIndexDE : DecidableEq (Slots w r) := Classical.decEq _

omit [Fintype (ℙ K (Dual K (Dual K V)))] [Nonempty (ℙ K V)]
  [Nonempty (ℙ K (Dual K V))] [Nonempty (ℙ K (Dual K (Dual K V)))]
  [Nonempty (Fin r)] in
theorem high_domain_good_pair_loss (hdim : finrank K V=5)
    (D : Slots w r→Finset (FlagPair K V))
    (p : Law (Slots w r→FlagPair K V))
    (hD : ∀ i,support (map p (fun x=>x i))⊆D i)
    (r' : ℕ) (hr' : r'≤4) (hcap : ∀i,HighCaps (D i) 4 r')
    (hcons : ∀ x,0<p x→∀ i j,slotEmbedding i<slotEmbedding j→
      Incident (x i).1 (x j).2→Incident (x j).1 (x i).2)
    (hflag : ∀ x,0<p x→∀ i,Incident (x i).1 (x i).2)
    (J d s ε : ℝ) (hJ : 4*Real.log (Nat.card K)≤J) (hs : 0<s)
    (hbad : highBadMass s d 153≤(1:ℝ)/4)
    (hsmall : 2*(Nat.card K:ℝ)^2*(2*Real.exp s/(Nat.card K:ℝ)^4)≤1/(20*(Nat.card K:ℝ)))
    (c : Slots w r→Slots w r→ℝ) (hc : ∀ i j,0≤c i j) (hcs : ∀ i j,c i j=c j i)
    (sel : (Fin w×Bool)→Fin r) (v : Fin w) (t : Fin (2*r))
    (hready : windowReady (indexBad J d ε p c sel) sel v t) (h : ℕ) :
    mean (map p (fun x=>x (Sum.inr (v,t)))) (fun z=>eventWeight
      (iid (iid (highRepresentative (map p (fun x=>x (Sum.inl ((v,false),sel (v,false))))) 4 r' s)
        (Fin h)) (Fin 3)) (fun x=>z∉highDomain x))≤
      highBadMass s d 153+64*(Nat.card K:ℝ)^5*(2*Real.exp s/(Nat.card K:ℝ)^r')*
        (Real.exp s/(Nat.card K:ℝ)^4)+3*(1-1/(5*(Nat.card K:ℝ)))^h+12*h*ε := by
  let i : Slots w r:=Sum.inl ((v,false),sel (v,false))
  let j : Slots w r:=Sum.inr (v,t)
  let q:=pair p (fun x=>x i) (fun x=>x j)
  have hqi : first q=map p (fun x=>x i) := first_pair p _ _
  have hqj : second q=map p (fun x=>x j) := second_pair p _ _
  have hi:=good_index_scores J d ε p c hc sel i (hready.2 false)
  have hj:=good_index_scores J d ε p c hc sel j hready.1
  have hI:=good_index_scores_reverse J d ε p c hc hcs sel j hready.1 (v,false) trivial
  have hIc : entropy (first q)+entropy (second q)-entropy q≤ε := by
    rw [hqi,hqj]
    exact le_trans (le_add_of_nonneg_right (hc i j)) hI
  have hpc : ∀ z,0<q z→Incident z.1.1 z.2.2→Incident z.2.1 z.1.2 := by
    intro z hz
    obtain ⟨x,hx,he⟩:=map_positive p (fun x=>(x i,x j)) z hz
    cases he
    exact hcons x hx i j (representative_early v (sel (v,false)) t)
  have hpf : ∀ z,0<second q z→Incident z.1 z.2 := by
    intro z hz
    rw [hqj] at hz
    obtain ⟨x,hx,he⟩:=map_positive p (fun x=>x j) z hz
    cases he
    exact hflag x hx j
  have H:=high_domain_pair_loss hdim (D i) (D j) r' hr' (hcap i) (hcap j) q
    (hqi ▸ hD i) (hqj ▸ hD j)
    hpc hpf s d ε hs (by rw [hqi]; linarith [hi.1])
    (by rw [hqj]; linarith [hj.1]) hbad hIc hsmall h
  simpa only [hqi,hqj,i,j] using H
end

end SharpRamseyFive.Marking

end OAI
