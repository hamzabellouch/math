import Mathlib
import OAI.Combinatorics.RamseyFive.Entropy.GoodRepresentative
import OAI.Combinatorics.RamseyFive.Decoding.HighSampleDecoder
import OAI.Combinatorics.RamseyFive.Entropy.IndependentSampling
import OAI.Combinatorics.RamseyFive.Entropy.HighEndpointCutoffs

namespace OAI

namespace SharpRamseyFive.HighSamples
open Module SharpRamseyFive.ProjectiveIncidence SharpRamseyFive.FiniteEntropy
open scoped Classical BigOperators LinearAlgebra.Projectivization
noncomputable section
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]

def SampleConflict (w z : SampleFlag (K:=K) (V:=V)) : Prop :=
  Incident w.1 z.2 ∧ ¬Incident z.1 w.2

theorem fixed_target_loss (p : Law (SampleFlag (K:=K) (V:=V)))
    (z : SampleFlag (K:=K) (V:=V)) (hz : Incident z.1 z.2)
    (C : ℝ) (hC : 0≤C) (hp : ∀ b,second p b≤C)
    (hy : z.2∉lowHits (first p))
    (hsmall : 2*(Nat.card K:ℝ)^2*C≤1/(20*(Nat.card K:ℝ))) (n : ℕ) :
    eventWeight (iid (iid p (Fin n)) (Fin 3)) (fun x=>z∉highDomain x)≤
      3*(1-1/(5*(Nat.card K:ℝ)))^n+3*(n*eventWeight p (fun w=>SampleConflict w z)) := by
  have hsub : ∀ x : Fin 3→Fin n→SampleFlag (K:=K) (V:=V),z∉highDomain x →
      finrank K (sampleSpan x z.2)<4 ∨ ∃ j i,SampleConflict (x j i) z := by
    intro x hx
    by_cases hr : finrank K (sampleSpan x z.2)<4
    · exact Or.inl hr
    · apply Or.inr
      by_contra! hc
      apply hx
      apply mem_highDomain x z hz (by omega)
      intro j i hi
      by_contra hn
      exact hc j i ⟨hi,hn⟩
  apply (eventWeight_mono _ _ _ hsub).trans
  apply (eventWeight_union _ _ _).trans
  exact add_le_add (sampled_span_rank_failure p z.2 C hC hp hy hsmall n)
    (by simpa using iid_nested_exists_event (I:=Fin n) (J:=Fin 3) p (fun w=>SampleConflict w z))

omit [Finite K] [FiniteDimensional K V] in
lemma mean_second (r : Law (SampleFlag (K:=K) (V:=V))) (f : ℙ K (Dual K V)→ℝ) :
    mean r (fun z=>f z.2)=mean (second r) f := by
  simp only [mean,second,Fintype.sum_prod_type,Finset.sum_mul]
  exact Finset.sum_comm

omit [Finite K] [FiniteDimensional K V] in
lemma mean_sampleConflict (p r : Law (SampleFlag (K:=K) (V:=V))) :
    mean r (fun z=>eventWeight p (fun w=>SampleConflict w z))=relationMass SampleConflict p r := by
  rw [relationMass_by_target]
  simp only [mean,eventWeight,Finset.sum_filter]

theorem sampled_target_loss (hdim : finrank K V=5)
    (p r : Law (SampleFlag (K:=K) (V:=V)))
    (hrflag : ∀ z,0<r z→Incident z.1 z.2)
    (G : Finset (ℙ K (Dual K V))) (A B C : ℝ)
    (hA : 0≤A) (hB : 0≤B) (hC : 0≤C)
    (hpA : ∀ a,first p a≤A) (hrB : ∀ b∈G,second r b≤B) (hpC : ∀ b,second p b≤C)
    (hsmall : 2*(Nat.card K:ℝ)^2*C≤1/(20*(Nat.card K:ℝ))) (n : ℕ) :
    mean r (fun z=>eventWeight (iid (iid p (Fin n)) (Fin 3)) (fun x=>z∉highDomain x)) ≤
      eventMass (second r) Gᶜ+64*(Nat.card K:ℝ)^5*A*B+
      3*(1-1/(5*(Nat.card K:ℝ)))^n+3*n*relationMass SampleConflict p r := by
  let E : ℝ:=3*(1-1/(5*(Nat.card K:ℝ)))^n
  have hq : 2≤(Nat.card K:ℝ) := by exact_mod_cast Finite.one_lt_card (α:=K)
  have hc : 0≤1-1/(5*(Nat.card K:ℝ)) := by
    have hh : 1/(5*(Nat.card K:ℝ))≤1 := (div_le_one (by positivity)).mpr (by linarith)
    linarith
  have hE : 0≤E := mul_nonneg (by norm_num) (pow_nonneg hc _)
  have hpoint : mean r (fun z=>eventWeight (iid (iid p (Fin n)) (Fin 3)) (fun x=>z∉highDomain x)) ≤
      mean r (fun z=>(if z.2∈lowHits (first p) then 1 else 0)+E+
        3*n*eventWeight p (fun w=>SampleConflict w z)) := by
    apply Finset.sum_le_sum
    intro z _
    by_cases hz : 0<r z
    · apply mul_le_mul_of_nonneg_left _ (r.nonneg z)
      dsimp only
      by_cases hy : z.2∈lowHits (first p)
      · rw [ite_eq_left hy]
        have hn : 0≤3*(n:ℝ)*eventWeight p (fun w=>SampleConflict w z) :=
          mul_nonneg (by positivity) (eventWeight_nonneg _ _)
        linarith [eventWeight_le_one (iid (iid p (Fin n)) (Fin 3)) (fun x=>z∉highDomain x)]
      · rw [ite_eq_right hy,zero_add]
        simpa only [mul_assoc] using fixed_target_loss p z (hrflag z hz) C hC hpC hy hsmall n
    · have hz' : r z=0 := le_antisymm (le_of_not_gt hz) (r.nonneg z)
      simp only [hz',zero_mul,le_refl]
  have he : mean r (fun z=>(if z.2∈lowHits (first p) then 1 else 0)+E+
        3*n*eventWeight p (fun w=>SampleConflict w z))=
      eventMass (second r) (lowHits (first p))+E+3*n*relationMass SampleConflict p r := by
    rw [mean_add,mean_add,mean_const,mean_smul,mean_sampleConflict]
    congr 2
    rw [mean_second r (fun b=>if b∈lowHits (first p) then (1:ℝ) else 0)]
    simp only [mean,eventMass,mul_ite,mul_one,mul_zero]
    symm
    calc
      _ = ∑ b∈lowHits (first p),if b∈lowHits (first p) then second r b else 0 := by
        apply Finset.sum_congr rfl
        intro b hb
        rw [ite_eq_left hb]
      _ = ∑ b,if b∈lowHits (first p) then second r b else 0 := by
        apply Finset.sum_subset (Finset.subset_univ _)
        intro b _ hb
        rw [ite_eq_right hb]
  have hl : eventMass (second r) (lowHits (first p)) ≤
      eventMass (second r) Gᶜ+64*(Nat.card K:ℝ)^5*A*B := by
    have hm := lowHits_mass hdim (first p) (second r) G A B hA hB
      (fun a=>⟨(first p).nonneg a,hpA a⟩) (by rw [(first p).sum_one];norm_num)
      (by rw [(first p).sum_one]) hrB
    have hh : eventMass (second r) (lowHits (first p))≤
        eventMass (second r) Gᶜ+eventMass (second r) (G∩lowHits (first p)) := by
      have he0 (S : Finset (ℙ K (Dual K V))) : eventMass (second r) S =
          eventWeight (second r) (fun b=>b∈S) := by
        unfold eventMass eventWeight
        calc
          _ = ∑ b∈S,if b∈S then second r b else 0 := by
            apply Finset.sum_congr rfl
            intro b hb
            rw [ite_eq_left hb]
          _ = ∑ b,if b∈S then second r b else 0 := by
            apply Finset.sum_subset (Finset.subset_univ _)
            intro b _ hb
            rw [ite_eq_right hb]
          _ = _ := by
            apply Finset.sum_congr rfl
            intro b _
            by_cases hb : b∈S <;> simp only [hb,ite_true,ite_false]
      simp only [he0,eventWeight,←Finset.sum_add_distrib]
      apply Finset.sum_le_sum
      intro b _
      by_cases hb : b∈G <;> by_cases hl : b∈lowHits (first p) <;>
        simp only [Finset.mem_compl,Finset.mem_inter,hb,hl,
          and_true,and_false,not_true_eq_false,not_false_eq_true,ite_true,ite_false,
          add_zero,zero_add,le_refl]
      exact (second r).nonneg b
    exact hh.trans (add_le_add le_rfl hm)
  rw [he] at hpoint
  exact hpoint.trans (add_le_add (add_le_add hl le_rfl) le_rfl)
end
end SharpRamseyFive.HighSamples

namespace SharpRamseyFive.Marking
open Module SharpRamseyFive.ProjectiveIncidence SharpRamseyFive.FiniteEntropy
open SharpRamseyFive.HighSamples
open scoped Classical LinearAlgebra.Projectivization BigOperators
noncomputable section
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
local instance highRepDE : DecidableEq (ℙ K V) := Classical.decEq _
local instance highRepDualDE : DecidableEq (ℙ K (Dual K V)) := Classical.decEq _

def highLeft (p : Law (FlagPair K V)) (r' : ℕ) (s : ℝ) : Finset (ℙ K V) :=
  highGoodFirst p (32*(Nat.card K:ℝ)^r') ((Nat.card K:ℝ)^4) ((Nat.card K:ℝ)^r') s
def highRight (p : Law (FlagPair K V)) (r : ℕ) (s : ℝ) : Finset (ℙ K (Dual K V)) :=
  highGoodFirst (swap p) (32*(Nat.card K:ℝ)^r) ((Nat.card K:ℝ)^4) ((Nat.card K:ℝ)^r) s

def highRepresentative (p : Law (FlagPair K V)) (r r' : ℕ) (s : ℝ) : Law (FlagPair K V) :=
  if h : 0<eventMass p (highLeft p r' s×ˢhighRight p r s) then
    conditionOn p (highLeft p r' s×ˢhighRight p r s) h else p

lemma highLeft_cap (p : Law (FlagPair K V)) (r' : ℕ) (s : ℝ) (a : ℙ K V)
    (ha : a∈highLeft p r' s) : first p a≤Real.exp s/(Nat.card K:ℝ)^r' := by
  have hq : 0<(Nat.card K:ℝ) := by exact_mod_cast Nat.zero_lt_of_lt (Finite.one_lt_card (α:=K))
  exact (le_div_iff₀ (pow_pos hq r')).mpr (by
    simpa only [mul_comm] using
      (Finset.mem_filter.mp (show a∈highGoodFirst _ _ _ _ _ from ha)).2)
lemma highRight_cap (p : Law (FlagPair K V)) (r : ℕ) (s : ℝ) (b : ℙ K (Dual K V))
    (hb : b∈highRight p r s) : second p b≤Real.exp s/(Nat.card K:ℝ)^r := by
  have hq : 0<(Nat.card K:ℝ) := by exact_mod_cast Nat.zero_lt_of_lt (Finite.one_lt_card (α:=K))
  have hh:=(Finset.mem_filter.mp (show b∈highGoodFirst _ _ _ _ _ from hb)).2
  rw [first_swap] at hh
  exact (le_div_iff₀ (pow_pos hq r)).mpr (by simpa only [mul_comm] using hh)

omit [Finite K] in
lemma high_pair_half (p : Law (FlagPair K V)) (r r' : ℕ) (s b : ℝ)
    (ha : eventMass (first p) (highLeft p r' s)ᶜ≤b)
    (hb : eventMass (second p) (highRight p r s)ᶜ≤b) (hsmall : b≤(1:ℝ)/4) :
    (1:ℝ)/2≤eventMass p (highLeft p r' s×ˢhighRight p r s) := by
  have h:=good_pair_mass p (highLeft p r' s) (highRight p r s)
  linarith

theorem highRepresentative_bounds (p : Law (FlagPair K V)) (r r' : ℕ) (s : ℝ)
    (hhalf : (1:ℝ)/2≤eventMass p (highLeft p r' s×ˢhighRight p r s)) :
    (∀ z,highRepresentative p r r' s z≤2*p z) ∧
    (∀ a,first (highRepresentative p r r' s) a≤2*Real.exp s/(Nat.card K:ℝ)^r') ∧
    (∀ b,second (highRepresentative p r r' s) b≤2*Real.exp s/(Nat.card K:ℝ)^r) := by
  have hpos : 0<eventMass p (highLeft p r' s×ˢhighRight p r s) := by linarith
  have he : highRepresentative p r r' s=
      goodRepresentative p (highLeft p r' s) (highRight p r s) hpos := by
    simp only [highRepresentative,dite_eq_left hpos,goodRepresentative]
  rw [he]
  constructor
  · intro z
    apply (conditionOn_le p _ hpos z).trans
    apply (div_le_iff₀ hpos).mpr
    nlinarith [p.nonneg z]
  constructor
  · intro a
    apply (goodRepresentative_first_cap p _ _ hpos (Real.exp s/(Nat.card K:ℝ)^r')
      (by positivity) (highLeft_cap p r' s) a).trans
    apply (div_le_iff₀ hpos).mpr
    have hz : 0≤Real.exp s/(Nat.card K:ℝ)^r' := by positivity
    have hs := mul_le_mul_of_nonneg_left hhalf (show 0≤2*(Real.exp s/(Nat.card K:ℝ)^r') by positivity)
    rw [mul_div_assoc]
    nlinarith only [hs]
  · intro b
    apply (goodRepresentative_second_cap p _ _ hpos (Real.exp s/(Nat.card K:ℝ)^r)
      (by positivity) (highRight_cap p r s) b).trans
    apply (div_le_iff₀ hpos).mpr
    have hz : 0≤Real.exp s/(Nat.card K:ℝ)^r := by positivity
    have hs := mul_le_mul_of_nonneg_left hhalf (show 0≤2*(Real.exp s/(Nat.card K:ℝ)^r) by positivity)
    rw [mul_div_assoc]
    nlinarith only [hs]

omit [Finite K] in
theorem highRepresentative_conflict (p : Law (FlagPair K V×FlagPair K V))
    (r r' : ℕ) (s ε : ℝ)
    (hcons : ∀ z,0<p z→Incident z.1.1 z.2.2→Incident z.2.1 z.1.2)
    (hhalf : (1:ℝ)/2≤eventMass (first p) (highLeft (first p) r' s×ˢhighRight (first p) r s))
    (hI : entropy (first p)+entropy (second p)-entropy p≤ε) :
    relationMass SampleConflict (highRepresentative (first p) r r' s) (second p)≤4*ε := by
  have hpos : 0<eventMass (first p) (highLeft (first p) r' s×ˢhighRight (first p) r s) := by linarith
  have hforbid:=forbidden_product_mass p SampleConflict (by
    intro z hz hc
    exact hc.2 (hcons z hz hc.1))
  have hI0 : 0≤entropy (first p)+entropy (second p)-entropy p := by
    linarith [entropy_subadditive p]
  have he0 : 0≤ε := hI0.trans hI
  simp only [highRepresentative,dite_eq_left hpos]
  apply (relationMass_conditionOn_left SampleConflict (first p) (second p) _ hpos).trans
  apply (div_le_iff₀ hpos).mpr
  have hm:=mul_le_mul_of_nonneg_left hhalf (show 0≤4*ε by positivity)
  linarith
end
end SharpRamseyFive.Marking

end OAI
