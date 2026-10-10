import Mathlib
import OAI.Combinatorics.RamseyFive.Entropy.BlockSelected
import OAI.Combinatorics.RamseyFive.Entropy.OriginalLevelLaw
import OAI.Combinatorics.RamseyFive.Geometry.ProjectiveExpectedLevelLoss
import OAI.Combinatorics.RamseyFive.Entropy.EventWeight

namespace OAI

namespace SharpRamseyFive.FiniteEntropy
open scoped Classical BigOperators
noncomputable section
variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]

lemma good_pair_mass (p : Law (α×β)) (A : Finset α) (B : Finset β) :
    1-eventMass (first p) Aᶜ-eventMass (second p) Bᶜ≤eventMass p (A×ˢB) := by
  have hs (z : α×β) : p z≤(if z∈A×ˢB then p z else 0)+
      (if z.1∈Aᶜ then p z else 0)+(if z.2∈Bᶜ then p z else 0) := by
    by_cases ha : z.1∈A <;> by_cases hb : z.2∈B <;>
      simp [ha,hb,Finset.mem_compl,Finset.mem_product]
    linarith [p.nonneg z]
  have hh:=Finset.sum_le_sum (s:=Finset.univ) (fun z _=>hs z)
  have hA : (∑ z:α×β,if z.1∈Aᶜ then p z else 0)=eventMass (first p) Aᶜ := by
    simp only [Fintype.sum_prod_type,eventMass,first]
    calc
      _ = ∑ a,if a∈Aᶜ then ∑ b,p (a,b) else 0 := by
        apply Finset.sum_congr rfl
        intro a _
        split_ifs <;> simp only [Finset.sum_const_zero]
      _ = _ := by rw [Finset.sum_ite_mem,Finset.univ_inter]
  have hB : (∑ z:α×β,if z.2∈Bᶜ then p z else 0)=eventMass (second p) Bᶜ := by
    rw [Fintype.sum_prod_type,Finset.sum_comm]
    simp only [eventMass,second]
    calc
      _ = ∑ b,if b∈Bᶜ then ∑ a,p (a,b) else 0 := by
        apply Finset.sum_congr rfl
        intro b _
        split_ifs <;> simp only [Finset.sum_const_zero]
      _ = _ := by rw [Finset.sum_ite_mem,Finset.univ_inter]
  simp only [Finset.sum_add_distrib,p.sum_one,hA,hB,Finset.sum_ite_mem,Finset.univ_inter] at hh
  change 1≤eventMass p (A×ˢB)+eventMass (first p) Aᶜ+eventMass (second p) Bᶜ at hh
  linarith only [hh]

def goodRepresentative (p : Law (α×β)) (A : Finset α) (B : Finset β)
    (h : 0<eventMass p (A×ˢB)) : Law (α×β) := conditionOn p (A×ˢB) h

lemma goodRepresentative_first_cap (p : Law (α×β)) (A : Finset α) (B : Finset β)
    (h : 0<eventMass p (A×ˢB)) (M : ℝ) (hM : 0≤M)
    (hcap : ∀ a∈A,first p a≤M) (a : α) :
    first (goodRepresentative p A B h) a≤M/eventMass p (A×ˢB) := by
  by_cases ha : a∈A
  · apply le_trans _ (div_le_div_of_nonneg_right (hcap a ha) h.le)
    change (∑ b,conditionOn p (A×ˢB) h (a,b))≤(∑ b,p (a,b))/eventMass p (A×ˢB)
    rw [Finset.sum_div]
    exact Finset.sum_le_sum fun b _=>conditionOn_le p _ h (a,b)
  · have hz : first (goodRepresentative p A B h) a=0 := by
      simp only [first,goodRepresentative,conditionOn_apply,Finset.mem_product,ha,false_and,
        ite_false,Finset.sum_const_zero]
    rw [hz]
    exact div_nonneg hM h.le

lemma goodRepresentative_second_cap (p : Law (α×β)) (A : Finset α) (B : Finset β)
    (h : 0<eventMass p (A×ˢB)) (M : ℝ) (hM : 0≤M)
    (hcap : ∀ b∈B,second p b≤M) (b : β) :
    second (goodRepresentative p A B h) b≤M/eventMass p (A×ˢB) := by
  by_cases hb : b∈B
  · apply le_trans _ (div_le_div_of_nonneg_right (hcap b hb) h.le)
    change (∑ a,conditionOn p (A×ˢB) h (a,b))≤(∑ a,p (a,b))/eventMass p (A×ˢB)
    rw [Finset.sum_div]
    exact Finset.sum_le_sum fun a _=>conditionOn_le p _ h (a,b)
  · have hz : second (goodRepresentative p A B h) b=0 := by
      simp only [second,goodRepresentative,conditionOn_apply,Finset.mem_product,hb,and_false,
        ite_false,Finset.sum_const_zero]
    rw [hz]
    exact div_nonneg hM h.le

lemma relationMass_conditionOn_left (R : α→β→Prop) (p : Law α) (q : Law β)
    (E : Finset α) (h : 0<eventMass p E) :
    relationMass R (conditionOn p E h) q≤relationMass R p q/eventMass p E := by
  unfold relationMass
  rw [Finset.sum_div]
  apply Finset.sum_le_sum
  intro z _
  simpa only [div_mul_eq_mul_div] using
    mul_le_mul_of_nonneg_right (conditionOn_le p E h z.1) (q.nonneg z.2)

lemma forbidden_product_mass (p : Law (α×β)) (R : α→β→Prop)
    (h : ∀ z,0<p z→¬R z.1 z.2) :
    relationMass R (first p) (second p)≤
      2*(entropy (first p)+entropy (second p)-entropy p) := by
  have hz : eventWeight p (fun z=>R z.1 z.2)=0 := by
    apply eventWeight_zero
    intro z hz
    exact le_antisymm (le_of_not_gt (fun hp=>h z hp hz)) (p.nonneg z)
  have hh:=eventWeight_comparison p (product (first p) (second p)) (ac_product p) (fun z=>R z.1 z.2)
  rw [hz,add_zero,mutual_information] at hh
  simpa only [relationMass,Finset.sum_filter,eventWeight,product] using hh
end

noncomputable section
variable {α β : Type*} [Fintype α] [Fintype β]

lemma conditionOn_ge_on (p : Law α) (E : Finset α) (hE : 0<eventMass p E)
    (a : α) (ha : a∈E) : p a≤conditionOn p E hE a := by
  rw [conditionOn_apply,ite_eq_left ha]
  exact (le_div_iff₀ hE).mpr (mul_le_of_le_one_right (p.nonneg a) (eventMass_le_one p E))

omit [Fintype α] in
lemma uniformWeight_eq_zero_of_not_mem (A : Finset α) (a : α) (h : a∉A) :
    uniformWeight A a=0 := by simp only [uniformWeight,ite_eq_right h]

lemma supported_levels_conditioned_domination (μ : Law (Finset α)) (p : Law α)
    (E : Finset α) (hE : 0<eventMass p E) (C : ℝ) (hC : 0≤C)
    (hsub : ∀ A,0<μ A→A⊆E)
    (hdom : ∀ a,(∑ A,μ A*uniformWeight A a)≤C*p a) :
    ∀ a,(∑ A,positiveLaw μ A*uniformWeight A.val a)≤C*conditionOn p E hE a := by
  intro a
  rw [positiveLaw_mean μ (fun A=>uniformWeight A a)]
  by_cases ha : a∈E
  · exact (hdom a).trans (mul_le_mul_of_nonneg_left (conditionOn_ge_on p E hE a ha) hC)
  · have hz : (∑ A,μ A*uniformWeight A a)=0 := by
      apply Finset.sum_eq_zero
      intro A _
      by_cases hm : 0<μ A
      · rw [uniformWeight_eq_zero_of_not_mem A a (fun hx=>ha (hsub A hm hx)),mul_zero]
      · rw [le_antisymm (le_of_not_gt hm) (μ.nonneg A),zero_mul]
    rw [hz]
    exact mul_nonneg hC ((conditionOn p E hE).nonneg a)

lemma relationMass_conditioned_good (R : α→β→Prop) (p : Law α) (q : Law β)
    (A : Finset α) (B : Finset β) (hA : 0<eventMass p A) (hB : 0<eventMass q B) :
    relationMass R (conditionOn p A hA) (conditionOn q B hB)=
      relationMass (fun a b=>a∈A ∧ b∈B ∧ R a b) p q/(eventMass p A*eventMass q B) := by
  simp only [relationMass,Finset.sum_filter,conditionOn_apply]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro z _
  by_cases ha : z.1∈A <;> by_cases hb : z.2∈B <;> by_cases hr : R z.1 z.2 <;>
    simp only [ha,hb,hr,ite_true,ite_false,true_and,false_and,and_false,
      zero_mul,mul_zero,zero_div,div_mul_div_comm]
end
end SharpRamseyFive.FiniteEntropy

namespace SharpRamseyFive.ProjectiveIncidence
open Module FiniteEntropy
open scoped Classical LinearAlgebra.Projectivization BigOperators
noncomputable section
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]

theorem good_endpoint_supports (hdim : finrank K V=5)
    (p : Law ((ℙ K V)×(ℙ K (Dual K V))))
    (hp : ∀z,0<p z→Incident z.1 z.2) (NA NB C k δ b : ℝ)
    (hNA : 0<NA) (hNB : 0<NB) (hC : 0<C) (hk : 0<k)
    (hA : ((support (first p)).card:ℝ)≤NA)
    (hB : ((support (second p)).card:ℝ)≤NB)
    (hprod : NA*NB≤C^2*(Nat.card K:ℝ)^5)
    (hent : 4*Real.log (Nat.card K)-entropy p≤δ)
    (GA : Finset (ℙ K V)) (GB : Finset (ℙ K (Dual K V)))
    (hGA : eventMass (first p) GAᶜ≤b) (hGB : eventMass (second p) GBᶜ≤b)
    (hGApos : 0<eventMass (first p) GA) (hGBpos : 0<eventMass (second p) GB)
    (hsmall : 2*(δ+Real.log C+Real.log (C+1)+
      2*(Real.log (5*Real.log (Nat.card K)+1)+1))/k+2*Real.exp 1*b≤(1:ℝ)/2) :
    ∃μ : Law (Finset (ℙ K V)), ∃ν : Law (Finset (ℙ K (Dual K V))),
      (∀A,0<μ A→A.Nonempty ∧ A⊆GA ∧ NA*Real.exp (-k)/2≤(A.card:ℝ) ∧ (A.card:ℝ)≤NA) ∧
      (∀B,0<ν B→B.Nonempty ∧ B⊆GB ∧ NB*Real.exp (-k)/2≤(B.card:ℝ) ∧ (B.card:ℝ)≤NB) ∧
      (∀a,(∑A,positiveLaw μ A*uniformWeight A.val a)≤
        4*Real.exp 1*conditionOn (first p) GA hGApos a) ∧
      (∀b,(∑B,positiveLaw ν B*uniformWeight B.val b)≤
        4*Real.exp 1*conditionOn (second p) GB hGBpos b) := by
  obtain ⟨μ,ν,hμ,hν,hdomμ,hdomν⟩:=endpoint_supports hdim p hp NA NB C k δ b
    hNA hNB hC hk hA hB hprod hent GA GB hGA hGB hsmall
  refine ⟨μ,ν,?_,?_,?_,?_⟩
  · intro A hA
    have ha:=hμ A hA
    have hn : 0<(A.card:ℝ):=(by positivity : 0<NA*Real.exp (-k)/2).trans_le ha.2.1
    exact ⟨Finset.card_pos.mp (by exact_mod_cast hn),ha⟩
  · intro B hB
    have hb:=hν B hB
    have hn : 0<(B.card:ℝ):=(by positivity : 0<NB*Real.exp (-k)/2).trans_le hb.2.1
    exact ⟨Finset.card_pos.mp (by exact_mod_cast hn),hb⟩
  · exact supported_levels_conditioned_domination μ (first p) GA hGApos (4*Real.exp 1)
      (by positivity) (fun A hA=>(hμ A hA).1) hdomμ
  · exact supported_levels_conditioned_domination ν (second p) GB hGBpos (4*Real.exp 1)
      (by positivity) (fun B hB=>(hν B hB).1) hdomν
end
end SharpRamseyFive.ProjectiveIncidence

end OAI
