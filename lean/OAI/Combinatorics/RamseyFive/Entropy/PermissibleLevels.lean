import Mathlib
import OAI.Combinatorics.RamseyFive.Entropy.FinitePiLaw

namespace OAI

namespace SharpRamseyFive.FiniteEntropy

section
open scoped BigOperators Classical
variable {α : Type*} [Fintype α]

noncomputable def levelLoss (p : Law α) (N : ℝ) (n : Level p) : ℝ :=
  Real.log (N/(levelCell p n).card)
noncomputable def levelBadMass (p : Law α) (Good : Finset α) (n : Level p) : ℝ :=
  ∑a∈levelCell p n\Good,p a
noncomputable def permissibleLevels (p : Law α) (Good : Finset α) (N K : ℝ) : Finset (Level p) :=
  Finset.univ.filter (fun n=>0<(levelCell p n).card ∧ levelLoss p N n≤K ∧
    (levelCell p n).card≤2*(levelCell p n∩Good).card)

lemma levelBadMass_nonneg (p : Law α) (Good : Finset α) (n : Level p) :
    0≤levelBadMass p Good n := Finset.sum_nonneg (fun a _=>p.nonneg a)

lemma sum_levelBadMass (p : Law α) (Good : Finset α) :
    (∑n : Level p,levelBadMass p Good n)=eventMass p Goodᶜ := by
  have hs (n : Level p) : levelCell p n\Good=
      Finset.univ.filter (fun a=>0<p a ∧ atomLevel p a=n.val ∧ a∉Good) := by
    ext a
    simp [levelCell,and_assoc]
  simp only [levelBadMass,hs,Finset.sum_filter]
  rw [Finset.sum_comm]
  unfold eventMass
  rw [show Goodᶜ=Finset.univ.filter (fun a=>a∉Good) by ext a;simp,
    Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro a _
  by_cases hp : p a=0
  · simp [hp]
  · have hp0 : 0<p a := lt_of_le_of_ne (p.nonneg _) (Ne.symm hp)
    have he (n : Level p) : atomLevel p a=n.val ↔ levelIndex p a=n := by
      change (levelIndex p a).val=n.val ↔ _
      exact Subtype.ext_iff.symm
    by_cases ha : a∈Good <;> simp [hp0,he,ha]

lemma levelLoss_nonneg (p : Law α) (N : ℝ) (hN : 0<N)
    (hcap : ∀n : Level p,((levelCell p n).card:ℝ)≤N) (n : Level p) :
    0≤levelLoss p N n := by
  by_cases hz : (levelCell p n).card=0
  · simp [levelLoss,hz]
  · have hn : (0:ℝ)<(levelCell p n).card := by exact_mod_cast Nat.pos_of_ne_zero hz
    exact (Real.log_nonneg_iff (div_pos hN hn)).mpr
      ((le_div_iff₀ hn).mpr (by simpa using hcap n))

lemma thin_level_mass (p : Law α) (Good : Finset α) (n : Level p)
    (hthin : 2*(levelCell p n∩Good).card<(levelCell p n).card) :
    levelLaw p n≤2*Real.exp 1*levelBadMass p Good n := by
  have hsplit := Finset.card_sdiff_add_card_inter (levelCell p n) Good
  have hbad : 0<(levelCell p n\Good).card := by omega
  have hbn : (0:ℝ)<(levelCell p n\Good).card := by exact_mod_cast hbad
  have hc : ((levelCell p n).card:ℝ)≤2*(levelCell p n\Good).card := by exact_mod_cast (show (levelCell p n).card≤2*(levelCell p n\Good).card by omega)
  have hs := Finset.sum_le_sum (s:=levelCell p n\Good) (fun a ha=>
    level_mass_bound p n (Finset.mem_sdiff.mp ha).1)
  have he : (∑a∈levelCell p n\Good,(levelCell p n).card*Real.exp 1*p a)=
      (levelCell p n).card*Real.exp 1*levelBadMass p Good n := by rw [levelBadMass,Finset.mul_sum]
  rw [he] at hs
  simp only [Finset.sum_const,Finset.card_sdiff, nsmul_eq_mul] at hs
  have hu := mul_le_mul_of_nonneg_right hc
    (mul_nonneg (Real.exp_pos 1).le (levelBadMass_nonneg p Good n))
  have hs' : ((levelCell p n\Good).card:ℝ)*levelLaw p n≤
      (levelCell p n).card*Real.exp 1*levelBadMass p Good n := by simpa [Finset.card_sdiff] using hs
  apply (mul_le_mul_iff_right₀ hbn).mp
  nlinarith

theorem permissible_mass (p : Law α) (Good : Finset α) (N K : ℝ)
    (hN : 0<N) (hK : 0<K) (hcap : ∀n : Level p,((levelCell p n).card:ℝ)≤N) :
    1-(∑n : Level p,levelLaw p n*levelLoss p N n)/K-
      2*Real.exp 1*eventMass p Goodᶜ ≤
      eventMass (levelLaw p) (permissibleLevels p Good N K) := by
  have hpoint (n : Level p) :
      levelLaw p n≤(if n∈permissibleLevels p Good N K then levelLaw p n else 0)+
        levelLaw p n*levelLoss p N n/K+2*Real.exp 1*levelBadMass p Good n := by
    have hm := (levelLaw p).nonneg n
    have hl := levelLoss_nonneg p N hN hcap n
    have hb := levelBadMass_nonneg p Good n
    by_cases hn : n∈permissibleLevels p Good N K
    · rw [ite_eq_left hn]
      have h₁ : 0≤levelLaw p n*levelLoss p N n/K := div_nonneg (mul_nonneg hm hl) hK.le
      have h₂ : 0≤2*Real.exp 1*levelBadMass p Good n := by positivity
      linarith
    · rw [ite_eq_right hn,zero_add]
      simp only [permissibleLevels,Finset.mem_filter,Finset.mem_univ,true_and,not_and] at hn
      by_cases hz : (levelCell p n).card=0
      · have he : levelLaw p n=0 := by rw [level_mass];simp [Finset.card_eq_zero.mp hz]
        rw [he];positivity
      · have hn0 := Nat.pos_of_ne_zero hz
        by_cases hk : levelLoss p N n≤K
        · have hthin : 2*(levelCell p n∩Good).card<(levelCell p n).card := by
            exact Nat.lt_of_not_ge (hn hn0 hk)
          have hh := thin_level_mass p Good n hthin
          have : 0≤levelLaw p n*levelLoss p N n/K := div_nonneg (mul_nonneg hm hl) hK.le
          linarith
        · have hk' : K≤levelLoss p N n := (lt_of_not_ge hk).le
          have hlarge : levelLaw p n≤levelLaw p n*levelLoss p N n/K := by
            apply (le_div_iff₀ hK).mpr
            exact mul_le_mul_of_nonneg_left hk' hm
          have : 0≤2*Real.exp 1*levelBadMass p Good n := by positivity
          linarith
  have hh := Finset.sum_le_sum (fun n (_ : n∈Finset.univ)=>hpoint n)
  rw [(levelLaw p).sum_one,Finset.sum_add_distrib,Finset.sum_add_distrib,
    Finset.sum_ite_mem,Finset.univ_inter,←Finset.sum_div,←Finset.mul_sum,
    sum_levelBadMass] at hh
  change 1≤eventMass (levelLaw p) (permissibleLevels p Good N K)+_+_ at hh
  linarith

end

open scoped BigOperators Classical
variable {α β : Type*} [Fintype α] [Fintype β]

lemma positive_map_exists (p : Law α) (f : α→β) {b : β} (hb : 0 < map p f b) :
    ∃a,0 < p a ∧ f a=b := by
  have hnon : ∀a∈Finset.univ,(0:ℝ) ≤ if f a=b then p a else 0 := by
    intro a _;split
    · exact p.nonneg a
    · exact le_rfl
  obtain ⟨a,_,ha⟩ := (Finset.sum_pos_iff_of_nonneg hnon).mp hb
  split_ifs at ha with he
  · exact ⟨a,ha,he⟩
  · linarith

lemma permissible_support_size (p : Law α) (Good : Finset α) (N K : ℝ)
    (hN : 0 < N) (hcap : ∀n : Level p,((levelCell p n).card:ℝ) ≤ N)
    {n : Level p} (hn : n∈permissibleLevels p Good N K) :
    N*Real.exp (-K)/2 ≤ ((levelCell p n∩Good).card:ℝ) ∧
      ((levelCell p n∩Good).card:ℝ) ≤ N := by
  obtain ⟨hn0,hl,hh⟩ := (Finset.mem_filter.mp hn).2
  have hc : (0:ℝ) < (levelCell p n).card := by exact_mod_cast hn0
  have he := Real.exp_le_exp.mpr hl
  rw [levelLoss,Real.exp_log (div_pos hN hc)] at he
  have hc₁ : N*Real.exp (-K) ≤ ((levelCell p n).card:ℝ) := by
    rw [Real.exp_neg,←div_eq_mul_inv]
    apply (div_le_iff₀ (Real.exp_pos K)).mpr
    have := (div_le_iff₀ hc).mp he
    nlinarith
  have hc₂ : ((levelCell p n).card:ℝ) ≤ 2*(levelCell p n∩Good).card := by exact_mod_cast hh
  constructor
  · linarith
  · exact (by exact_mod_cast Finset.card_le_card (Finset.inter_subset_left) :
      ((levelCell p n∩Good).card:ℝ) ≤ (levelCell p n).card).trans (hcap n)

noncomputable def goodSupportLaw (p : Law α) (Good : Finset α) (N K : ℝ)
    (hE : (1:ℝ)/2 ≤ eventMass (levelLaw p) (permissibleLevels p Good N K)) : Law (Finset α) :=
  map (conditionOn (levelLaw p) (permissibleLevels p Good N K) (by linarith))
    (fun n=>levelCell p n∩Good)

theorem goodSupportLaw_bounds (p : Law α) (Good : Finset α) (N K : ℝ)
    (hN : 0 < N) (hcap : ∀n : Level p,((levelCell p n).card:ℝ) ≤ N)
    (hE : (1:ℝ)/2 ≤ eventMass (levelLaw p) (permissibleLevels p Good N K))
    (S : Finset α) (hS : 0 < goodSupportLaw p Good N K hE S) :
    S⊆Good ∧ N*Real.exp (-K)/2 ≤ (S.card:ℝ) ∧ (S.card:ℝ) ≤ N := by
  obtain ⟨n,hn,he⟩ := positive_map_exists _ _ hS
  have hm : n∈permissibleLevels p Good N K := by
    by_contra hh
    rw [conditionOn_apply,ite_eq_right hh] at hn
    exact lt_irrefl 0 hn
  subst S
  exact ⟨Finset.inter_subset_right,permissible_support_size p Good N K hN hcap hm⟩

theorem goodSupportLaw_domination (p : Law α) (Good : Finset α) (N K : ℝ)
    (hE : (1:ℝ)/2 ≤ eventMass (levelLaw p) (permissibleLevels p Good N K)) (a : α) :
    (∑S,goodSupportLaw p Good N K hE S*(if a∈S then 1/(S.card:ℝ) else 0)) ≤
      4*Real.exp 1*p a := by
  unfold goodSupportLaw
  rw [sum_map]
  exact good_level_domination p Good _ hE
    (fun n hn=>(Finset.mem_filter.mp hn).2.2.2) a

lemma permissible_half_mass (p : Law α) (Good : Finset α) (N K : ℝ)
    (hN : 0 < N) (hK : 0 < K) (hcap : ∀n : Level p,((levelCell p n).card:ℝ) ≤ N)
    (hsmall : (∑n : Level p,levelLaw p n*levelLoss p N n)/K+
      2*Real.exp 1*eventMass p Goodᶜ ≤ (1:ℝ)/2) :
    (1:ℝ)/2 ≤ eventMass (levelLaw p) (permissibleLevels p Good N K) := by
  have := permissible_mass p Good N K hN hK hcap
  linarith

end SharpRamseyFive.FiniteEntropy

end OAI
