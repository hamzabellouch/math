import Mathlib
import OAI.Combinatorics.SharpRamsey.Validation.ValidationCosts
import OAI.Combinatorics.SharpRamsey.Validation.ValidationReverse

namespace OAI

section
namespace SharpLogRamsey.Validation
open Finset Real Incidence
open scoped Classical BigOperators
noncomputable section

lemma row_cost_sum {q P d e B H J : ℝ} {h : ℕ}
    (hq : 1 ≤ q) (hP : 200000 ≤ P) (hd : 0 ≤ d) (he : 0 ≤ e)
    (hB : 0 ≤ B) (hBP : B ≤ 7*P) (hJ : 0 ≤ J)
    (hh : (h:ℝ) ≤ 20*q*(d+2)+1) (hH : log (H+1) ≤ J*q) :
    2*((h:ℝ)*B+log 2+log (H+1))+log 3 ≤
      (710+2*J)*q*P*(d+e+P) := by
  have hr := row_cost hq (by linarith : 1 ≤ P) hd hB (by norm_num : (0:ℝ) ≤ 7)
    hJ hBP hh hH
  rw [show (100:ℝ)*7+2*J+10=710+2*J by ring] at hr
  apply hr.trans
  gcongr
  linarith

variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]
local instance flat_JoinedValidationGapCosts_1 : Fintype (Projectivization K V) := by
  letI : Finite V := Module.finite_of_finite K
  exact Fintype.ofFinite _
local instance flat_JoinedValidationGapCosts_2 : Finite (Module.Dual K V) := Module.finite_of_finite K
local instance flat_JoinedValidationGapCosts_3 : Fintype (Projectivization K (Module.Dual K V)) := Fintype.ofFinite _
local instance flat_JoinedValidationGapCosts_4 : Finite (Module.Dual K (Module.Dual K V)) := Module.finite_of_finite K
local instance flat_JoinedValidationGapCosts_5 : Fintype (Projectivization K (Module.Dual K (Module.Dual K V))) := Fintype.ofFinite _

lemma log_hundred : log (100:ℝ) ≤ 99 := by
  have hh := log_le_sub_one_of_pos (by norm_num : (0:ℝ)<100)
  norm_num at hh ⊢
  exact hh
lemma log_hundred_thousand : log (100000:ℝ) ≤ 99999 := by
  have hh := log_le_sub_one_of_pos (by norm_num : (0:ℝ)<100000)
  norm_num at hh ⊢
  exact hh

theorem return_gap_cover {r : ℕ} (hdim : Module.finrank K V=r+3)
    (descriptions : Finset (Finset (Projectivization K V)))
    (U : Finset (Projectivization K V))
    (UT : Finset (Projectivization K (Module.Dual K V))) (N t : ℕ)
    (hN : 0<N) (ht : 0<t) (hNU : N≤U.card) (htU : t≤UT.card)
    (P b : ℝ) (hP : 200000≤P) (hb : 0≤b) (hbP : b≤P)
    (hsize : ∀ W∈descriptions,(W.card:ℝ)≤N*exp (6*P))
    (hprod : (N:ℝ)*t≤2*(Nat.card K:ℝ)^(r+3))
    (hprodlo : (Nat.card K:ℝ)^(r+3)*exp (-b)≤(N:ℝ)*t) :
    ∃ caps : Finset (Finset (Projectivization K V)),
      (∀ F∈caps,F⊆U ∧ (F.card:ℝ)≤100000*(Nat.card K:ℝ)^(r+3)/t) ∧
      (∀ S T,S⊆U → S.card=N → T⊆UT → T.card=t →
        (incidenceCount S T:ℝ)≤(N:ℝ)*t/(1000000*Nat.card K) →
        (∃ W∈descriptions,(N:ℝ)/100≤(S∩W).card) →
        ∃ F∈caps,(99/100:ℝ)*N≤(S∩F).card) ∧
      log ((caps.card:ℝ)+1) ≤ log ((descriptions.card:ℝ)+1)+
        (1500+8*(r:ℝ))*(Nat.card K:ℝ)*P*
          (log ((U.card:ℝ)/N)+log ((UT.card:ℝ)/t)+P) := by
  obtain ⟨A,hs,hc,hl⟩ := return_cover hdim descriptions U UT N t hN ht hNU htU
    100 (6*P) b (by norm_num) (by positivity) hb hsize hprod hprodlo
  refine ⟨A,?_,?_,?_⟩
  · intro F hF
    refine ⟨(hs F hF).1,(hs F hF).2.trans ?_⟩
    gcongr
    norm_num
  · intro S T hSU hSN hTU hTt hsp hcap
    exact hc S T hSU hSN hTU hTt (by simpa only [show (10000:ℝ)*100=1000000 by norm_num] using hsp) hcap
  · let q : ℝ := Nat.card K
    let d := log ((U.card:ℝ)/N)
    let e := log ((UT.card:ℝ)/t)
    have hq : 1≤q := by
      change (1:ℝ)≤(Nat.card K:ℝ)
      exact_mod_cast Nat.card_pos (α:=K)
    have hn : (0:ℝ)<N := by exact_mod_cast hN
    have ht' : (0:ℝ)<t := by exact_mod_cast ht
    have hnu : (N:ℝ)≤U.card := by exact_mod_cast hNU
    have htu : (t:ℝ)≤UT.card := by exact_mod_cast htU
    have hd : 0≤d := log_nonneg ((le_div_iff₀ hn).mpr (by simpa using hnu))
    have he : 0≤e := log_nonneg ((le_div_iff₀ ht').mpr (by simpa using htu))
    have hB1 : 6*P+log 100≤7*P := by linarith only [log_hundred,hP]
    have hB2 : b+log ((1000:ℝ)*100)+log 2≤7*P := by
      have hh := log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)
      norm_num only [show (1000:ℝ)*100=100000 by norm_num]
      linarith only [hbP,hP,log_hundred_thousand,hh]
    have hH1 := pair_log_card (r+3) hdim
    have hH2 := pair_log_card (K:=K) (V:=Module.Dual K V) (r+3)
      (Subspace.dual_finrank_eq.trans hdim)
    have E1 := row_cost_sum hq hP he hd
      (add_nonneg (by positivity) (log_nonneg (by norm_num))) hB1
      (show 0≤2*((r+3:ℕ):ℝ)+2 by positivity)
      (scheduleLength_le (by linarith : 0≤q) ht' htu) hH1
    have E2 := row_cost_sum hq hP hd he
      (add_nonneg (add_nonneg hb (log_nonneg (by norm_num))) (log_nonneg (by norm_num))) hB2
      (show 0≤2*((r+3:ℕ):ℝ)+2 by positivity)
      (scheduleLength_le (by linarith : 0≤q) hn hnu) hH2
    have hz : 0≤q*P*(d+e+P) := by positivity
    simp only [Nat.cast_add,Nat.cast_ofNat] at E1 E2
    change log ((A.card:ℝ)+1) ≤ log ((descriptions.card:ℝ)+1)+(1500+8*(r:ℝ))*q*P*(d+e+P)
    dsimp only [q,d,e] at *
    have hcombined := add_le_add E1 E2
    ring_nf at hcombined hl hz ⊢
    linarith only [hl,hcombined,hz]

theorem reverse_gap_cover {r : ℕ} (hdim : Module.finrank K V=r+3)
    (descriptions : Finset (Finset (Projectivization K (Module.Dual K V))))
    (U : Finset (Projectivization K V))
    (UT : Finset (Projectivization K (Module.Dual K V))) (N t : ℕ)
    (hN : 0<N) (ht : 0<t) (hNU : N≤U.card) (htU : t≤UT.card)
    (P : ℝ) (hP : 200000≤P)
    (hsize : ∀ W∈descriptions,(W.card:ℝ)≤t*exp (6*P))
    (hprod : (N:ℝ)*t≤2*(Nat.card K:ℝ)^(r+3)) :
    ∃ caps : Finset (Finset (Projectivization K V)),
      (∀ F∈caps,F⊆U ∧ (F.card:ℝ)≤100000*(Nat.card K:ℝ)^(r+3)/t) ∧
      (∀ S T,S⊆U → S.card=N → T.card=t →
        (incidenceCount S T:ℝ)≤(N:ℝ)*t/(1000000*Nat.card K) →
        (∃ W∈descriptions,(t:ℝ)/100≤(T∩W).card) →
        ∃ F∈caps,(99/100:ℝ)*N≤(S∩F).card) ∧
      log ((caps.card:ℝ)+1) ≤ log ((descriptions.card:ℝ)+1)+
        (1500+8*(r:ℝ))*(Nat.card K:ℝ)*P*
          (log ((U.card:ℝ)/N)+log ((UT.card:ℝ)/t)+P) := by
  obtain ⟨A,hs,hc,hl⟩ := reverse_extend_fraction hdim descriptions U N t hN ht hNU
    100 (6*P) (by norm_num) (by positivity) hsize hprod
  refine ⟨A,?_,?_,?_⟩
  · simpa only [show (1000:ℝ)*100=100000 by norm_num] using hs
  · intro S T hSU hSN hTt hsp hcap
    exact hc S T hSU hSN hTt (by simpa only [show (10000:ℝ)*100=1000000 by norm_num] using hsp) hcap
  · let q : ℝ := Nat.card K
    let d := log ((U.card:ℝ)/N)
    let e := log ((UT.card:ℝ)/t)
    have hq : 1≤q := by
      change (1:ℝ)≤(Nat.card K:ℝ)
      exact_mod_cast Nat.card_pos (α:=K)
    have hn : (0:ℝ)<N := by exact_mod_cast hN
    have ht' : (0:ℝ)<t := by exact_mod_cast ht
    have hnu : (N:ℝ)≤U.card := by exact_mod_cast hNU
    have htu : (t:ℝ)≤UT.card := by exact_mod_cast htU
    have hd : 0≤d := log_nonneg ((le_div_iff₀ hn).mpr (by simpa using hnu))
    have he : 0≤e := log_nonneg ((le_div_iff₀ ht').mpr (by simpa using htu))
    have hB : 6*P+log 100≤7*P := by linarith only [log_hundred,hP]
    have hH := pair_log_card (K:=K) (V:=Module.Dual K V) (r+3)
      (Subspace.dual_finrank_eq.trans hdim)
    have E := row_cost_sum hq hP hd he
      (add_nonneg (by positivity) (log_nonneg (by norm_num))) hB
      (show 0≤2*((r+3:ℕ):ℝ)+2 by positivity)
      (scheduleLength_le (by linarith : 0≤q) hn hnu) hH
    have hz : 0≤q*P*(d+e+P) := by positivity
    have hr : 0≤(r:ℝ)*q*P*(d+e+P) := by positivity
    simp only [Nat.cast_add,Nat.cast_ofNat] at E
    change log ((A.card:ℝ)+1) ≤ log ((descriptions.card:ℝ)+1)+(1500+8*(r:ℝ))*q*P*(d+e+P)
    dsimp only [q,d,e] at *
    nlinarith only [hl,E,hz,hr]

end
end SharpLogRamsey.Validation

end

end OAI
