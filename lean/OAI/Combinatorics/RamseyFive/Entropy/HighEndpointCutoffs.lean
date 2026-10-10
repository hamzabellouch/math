import Mathlib
import OAI.Combinatorics.RamseyFive.Marking.ReciprocalLevelProducer

namespace OAI

namespace SharpRamseyFive.FiniteEntropy
open scoped Classical BigOperators
noncomputable section
variable {α β : Type*} [Fintype α] [Fintype β]

lemma first_entropy_of_partner_cap (p : Law (α×β)) (M : ℝ) (_hM : 0<M)
    (hpartner : ∀ a,0<first p a →
      (((support p).filter fun z=>z.1=a).card:ℝ)≤M) :
    entropy p ≤ entropy (first p)+Real.log M := by
  have hh := entropy_partition_bound p Prod.fst (fun _=>Real.log M) (by
    intro a ha
    rw [map_fst] at ha
    have hc:=hpartner a ha
    have hp : 0<(((support p).filter fun z=>z.1=a).card:ℝ) := by
      obtain ⟨z,hz,hf⟩ := map_positive p Prod.fst a (by simpa [map_fst] using ha)
      exact_mod_cast Finset.card_pos.mpr ⟨z,Finset.mem_filter.mpr ⟨(mem_support p z).mpr hz,hf⟩⟩
    exact Real.log_le_log hp hc)
  simpa only [map_fst,←Finset.sum_mul,(first p).sum_one,one_mul] using hh

theorem high_first_upper_tail (p : Law (α×β)) (N S M K : ℝ)
    (hN : 0<N) (hM : 0<M) (hK : 0<K)
    (hcap : ((support (first p)).card:ℝ)≤S)
    (hpartner : ∀ a,0<first p a →
      (((support p).filter fun z=>z.1=a).card:ℝ)≤M) :
    eventMass (first p) (Finset.univ.filter fun a=>N*first p a>Real.exp K) ≤
      (Real.log N+Real.log M-entropy p+S/N)/K := by
  have hh := first_entropy_of_partner_cap p M hM hpartner
  have ht := scaled_heavy_atom_mass (first p) N S K hN hK hcap
  change eventMass (first p) _ ≤ _ at ht
  apply ht.trans
  apply div_le_div_of_nonneg_right _ hK.le
  linarith

def highGoodFirst (p : Law (α×β)) (NA N U K : ℝ) : Finset α :=
  (goodFirstEndpoints p NA N K).filter fun a=>U*first p a≤Real.exp K

theorem high_bad_first_mass (p : Law (α×β)) (NA N U S M T K : ℝ)
    (hNA : 0<NA) (hN : 0<N) (hU : 0<U) (hM : 0<M) (hK : 0<K)
    (hA : ((support (first p)).card:ℝ)≤NA)
    (hS : ((support (first p)).card:ℝ)≤S)
    (hflag : ((support p).card:ℝ)≤T)
    (hpartner : ∀ a,0<first p a →
      (((support p).filter fun z=>z.1=a).card:ℝ)≤M) :
    eventMass (first p) (highGoodFirst p NA N U K)ᶜ ≤
      Real.exp (-K)+50*(Real.log N-entropy p+T/N)/K+
      (Real.log U+Real.log M-entropy p+S/U)/K := by
  let E := Finset.univ.filter fun a=>U*first p a>Real.exp K
  have hsub : (highGoodFirst p NA N U K)ᶜ ⊆ (goodFirstEndpoints p NA N K)ᶜ ∪ E := by
    intro a ha
    simp only [Finset.mem_compl,highGoodFirst,Finset.mem_filter] at ha
    by_cases hg : a∈goodFirstEndpoints p NA N K
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,lt_of_not_ge (fun hu=>ha ⟨hg,hu⟩)⟩)
    · exact Finset.mem_union_left _ (Finset.mem_compl.mpr hg)
  have hs : eventMass (first p) (highGoodFirst p NA N U K)ᶜ ≤
      eventMass (first p) (goodFirstEndpoints p NA N K)ᶜ+eventMass (first p) E := by
    apply (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun a _ _=>(first p).nonneg a)).trans
    have hh := Finset.sum_union_inter (s₁:=(goodFirstEndpoints p NA N K)ᶜ) (s₂:=E) (f:=fun a=>first p a)
    have hn : 0≤∑ a∈(goodFirstEndpoints p NA N K)ᶜ∩E,first p a :=
      Finset.sum_nonneg fun a _=>(first p).nonneg a
    change ∑ a∈(goodFirstEndpoints p NA N K)ᶜ∪E,first p a ≤
      (∑ a∈(goodFirstEndpoints p NA N K)ᶜ,first p a)+∑ a∈E,first p a
    linarith
  exact hs.trans (add_le_add (bad_first_endpoint_mass p NA N T K hNA hN hK hA hflag)
    (high_first_upper_tail p U S M K hU hM hK hS hpartner))

lemma support_first_subset_image (p : Law (α×β)) (D : Finset (α×β))
    (hD : support p⊆D) : support (first p)⊆D.image Prod.fst := by
  intro a ha
  obtain ⟨z,hz,hf⟩:=map_positive p Prod.fst a (by simpa only [map_fst] using (mem_support _ _).mp ha)
  exact Finset.mem_image.mpr ⟨z,hD ((mem_support _ _).mpr hz),hf⟩

lemma support_fiber_card (p : Law (α×β)) (D : Finset (α×β))
    (hD : support p⊆D) (a : α) :
    ((support p).filter fun z=>z.1=a).card≤(Finset.univ.filter fun b=>(a,b)∈D).card := by
  apply Finset.card_le_card_of_injOn Prod.snd
  · intro z hz
    obtain ⟨hz,he⟩:=Finset.mem_filter.mp hz
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,by simpa only [←he,Prod.mk.eta] using hD hz⟩
  · intro z hz y hy he
    exact Prod.ext ((Finset.mem_filter.mp hz).2.trans (Finset.mem_filter.mp hy).2.symm) he

def highBadMass (s d C0 : ℝ) : ℝ :=
  Real.exp (-s)+50*(d+C0)/s+(d+Real.log 2+32)/s

theorem high_endpoint_bad (p : Law (α×β)) (q s d C0 : ℝ) (r : ℕ)
    (hq : 0<q) (hs : 0<s) (hr : r≤4)
    (hcap : ((support (first p)).card:ℝ)≤32*q^r)
    (hflag : ((support p).card:ℝ)≤C0*q^4)
    (hpartner : ∀ a,0<first p a→
      (((support p).filter fun z=>z.1=a).card:ℝ)≤2*q^(4-r))
    (hent : 4*Real.log q-entropy p≤d) :
    eventMass (first p) (highGoodFirst p (32*q^r) (q^4) (q^r) s)ᶜ≤highBadMass s d C0 := by
  have hq0 : q≠0:=ne_of_gt hq
  have hpow : (r:ℝ)+(4-r:ℕ)=4 := by exact_mod_cast Nat.add_sub_of_le hr
  have hl : Real.log (q^r)+Real.log (2*q^(4-r))=4*Real.log q+Real.log 2 := by
    rw [Real.log_mul (by norm_num) (pow_ne_zero _ hq0),Real.log_pow,Real.log_pow]
    calc
      _ = ((r:ℝ)+(4-r:ℕ))*Real.log q+Real.log 2 := by ring
      _ = _ := by rw [hpow]
  have h:=high_bad_first_mass p (32*q^r) (q^4) (q^r) (32*q^r) (2*q^(4-r)) (C0*q^4) s
    (by positivity) (by positivity) (by positivity) (by positivity) hs hcap hcap hflag hpartner
  rw [Real.log_pow,hl,mul_div_cancel_right₀ _ (pow_ne_zero 4 hq0),
    mul_div_cancel_right₀ _ (pow_ne_zero r hq0)] at h
  apply h.trans
  unfold highBadMass
  exact add_le_add (add_le_add le_rfl (div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left (add_le_add hent (le_refl C0)) (by norm_num)) hs.le))
    (div_le_div_of_nonneg_right (by linarith) hs.le)

theorem high_endpoint_bad_of_domain (p : Law (α×β)) (D : Finset (α×β))
    (hD : support p⊆D) (q s d C0 : ℝ) (r : ℕ)
    (hq : 0<q) (hs : 0<s) (hr : r≤4)
    (hcap : ((D.image Prod.fst).card:ℝ)≤32*q^r)
    (hflag : (D.card:ℝ)≤C0*q^4)
    (hpartner : ∀ a,((Finset.univ.filter fun b=>(a,b)∈D).card:ℝ)≤2*q^(4-r))
    (hent : 4*Real.log q-entropy p≤d) :
    eventMass (first p) (highGoodFirst p (32*q^r) (q^4) (q^r) s)ᶜ≤highBadMass s d C0 := by
  apply high_endpoint_bad p q s d C0 r hq hs hr
  · exact (Nat.cast_le.mpr (Finset.card_le_card (support_first_subset_image p D hD))).trans hcap
  · exact (Nat.cast_le.mpr (Finset.card_le_card hD)).trans hflag
  · intro a _
    exact (Nat.cast_le.mpr (support_fiber_card p D hD a)).trans (hpartner a)
  · exact hent

lemma support_swap_first_fiber (p : Law (α×β)) (b : β) :
    ((support (swap p)).filter fun z=>z.1=b).card=
      ((support p).filter fun z=>z.2=b).card := by
  apply Finset.card_bij (fun z _=>z.swap)
  · intro z hz
    obtain ⟨hp,he⟩:=Finset.mem_filter.mp hz
    apply Finset.mem_filter.mpr
    refine ⟨(mem_support p _).mpr ?_,he⟩
    exact (mem_support (swap p) z).mp hp
  · intro z hz y hy he
    exact Prod.swap_injective he
  · intro z hz
    obtain ⟨hp,he⟩:=Finset.mem_filter.mp hz
    refine ⟨z.swap,Finset.mem_filter.mpr ⟨?_,he⟩,Prod.swap_swap _⟩
    apply (mem_support (swap p) _).mpr
    exact (mem_support p z).mp hp

theorem high_endpoint_bad_second (p : Law (α×β)) (q s d C0 : ℝ) (r : ℕ)
    (hq : 0<q) (hs : 0<s) (hr : r≤4)
    (hcap : ((support (second p)).card:ℝ)≤32*q^r)
    (hflag : ((support p).card:ℝ)≤C0*q^4)
    (hpartner : ∀ b,0<second p b→
      (((support p).filter fun z=>z.2=b).card:ℝ)≤2*q^(4-r))
    (hent : 4*Real.log q-entropy p≤d) :
    eventMass (second p) (highGoodFirst (swap p) (32*q^r) (q^4) (q^r) s)ᶜ≤highBadMass s d C0 := by
  have h:=high_endpoint_bad (swap p) q s d C0 r hq hs hr
    (by simpa only [first_swap] using hcap)
    (by simpa only [support_swap_card] using hflag)
    (by intro b hb; rw [support_swap_first_fiber]; exact hpartner b (by simpa only [first_swap] using hb))
    (by simpa only [entropy_swap] using hent)
  simpa only [first_swap] using h

lemma support_second_subset_image (p : Law (α×β)) (D : Finset (α×β))
    (hD : support p⊆D) : support (second p)⊆D.image Prod.snd := by
  intro b hb
  obtain ⟨z,hz,hf⟩:=map_positive p Prod.snd b (by simpa only [map_snd] using (mem_support _ _).mp hb)
  exact Finset.mem_image.mpr ⟨z,hD ((mem_support _ _).mpr hz),hf⟩

lemma support_second_fiber_card (p : Law (α×β)) (D : Finset (α×β))
    (hD : support p⊆D) (b : β) :
    ((support p).filter fun z=>z.2=b).card≤(Finset.univ.filter fun a=>(a,b)∈D).card := by
  apply Finset.card_le_card_of_injOn Prod.fst
  · intro z hz
    obtain ⟨hz,he⟩:=Finset.mem_filter.mp hz
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,by simpa only [←he,Prod.mk.eta] using hD hz⟩
  · intro z hz y hy he
    exact Prod.ext he ((Finset.mem_filter.mp hz).2.trans (Finset.mem_filter.mp hy).2.symm)

theorem high_endpoint_bad_second_of_domain (p : Law (α×β)) (D : Finset (α×β))
    (hD : support p⊆D) (q s d C0 : ℝ) (r : ℕ)
    (hq : 0<q) (hs : 0<s) (hr : r≤4)
    (hcap : ((D.image Prod.snd).card:ℝ)≤32*q^r)
    (hflag : (D.card:ℝ)≤C0*q^4)
    (hpartner : ∀ b,((Finset.univ.filter fun a=>(a,b)∈D).card:ℝ)≤2*q^(4-r))
    (hent : 4*Real.log q-entropy p≤d) :
    eventMass (second p) (highGoodFirst (swap p) (32*q^r) (q^4) (q^r) s)ᶜ≤highBadMass s d C0 := by
  apply high_endpoint_bad_second p q s d C0 r hq hs hr
  · exact (Nat.cast_le.mpr (Finset.card_le_card (support_second_subset_image p D hD))).trans hcap
  · exact (Nat.cast_le.mpr (Finset.card_le_card hD)).trans hflag
  · intro b _
    exact (Nat.cast_le.mpr (support_second_fiber_card p D hD b)).trans (hpartner b)
  · exact hent

lemma high_endpoint_atom (p : Law (α×β)) (q s : ℝ) (r : ℕ) (hq : 0<q)
    (a : α) (ha : a∈highGoodFirst p (32*q^r) (q^4) (q^r) s) :
    first p a≤Real.exp s/q^r := by
  exact (le_div_iff₀ (pow_pos hq r)).mpr (by simpa only [mul_comm] using (Finset.mem_filter.mp ha).2)

lemma high_endpoint_mass (p : Law (α×β)) (q s d C0 : ℝ) (r : ℕ)
    (hbad : eventMass (first p) (highGoodFirst p (32*q^r) (q^4) (q^r) s)ᶜ≤highBadMass s d C0)
    (hsmall : highBadMass s d C0≤(1:ℝ)/4) :
    (3:ℝ)/4≤eventMass (first p) (highGoodFirst p (32*q^r) (q^4) (q^r) s) := by
  have hc:=eventMass_complement (first p) (highGoodFirst p (32*q^r) (q^4) (q^r) s)
  linarith

end
end SharpRamseyFive.FiniteEntropy

end OAI
