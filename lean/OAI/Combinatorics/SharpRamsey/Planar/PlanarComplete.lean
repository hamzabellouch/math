import Mathlib
import OAI.Combinatorics.SharpRamsey.Planar.PlanarBoth

namespace OAI

section
namespace SharpLogRamsey.PlanarLearning
open Finset Real Filter SourceScales Incidence
open scoped Classical BigOperators Topology NNReal
noncomputable section
local instance flat_JoinedPlanarComplete_1 {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] : Finite (Module.Dual K V) := Module.finite_of_finite K
local instance flat_JoinedPlanarComplete_2 {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] : Fintype (Projectivization K V) := by
  letI : Finite V := Module.finite_of_finite K
  exact Fintype.ofFinite _

theorem complete_cover {η : ℝ} (hη : 0<η) (C : ℝ) (hC : 1≤C) :
    ∀ᶠ σ : ℝ in atTop,∀ (K V : Type) [Field K] [Finite K]
      [AddCommGroup V] [Module K V] [FiniteDimensional K V],
    ∀ D R,Admissible σ η D R → exp σ=(Nat.card K:ℝ) → Module.finrank K V=3 →
    ∀ (U : Finset (Projectivization K V))
      (UT : Finset (Projectivization K (Module.Dual K V))) (n t : ℕ) (b τ : ℝ),
    0<n → 0<t → n≤U.card → t≤UT.card → 0≤b → b≤C*scaleKstar σ η D →
    0<τ → τ≤C*σ^(-100*beta η) →
    (Nat.card K:ℝ)^3*exp (-b)≤(n:ℝ)*t → (n:ℝ)*t≤2*(Nat.card K:ℝ)^3 →
    let P := scaleP σ η D R
    ∃ caps : Finset (Finset (Projectivization K V)),
      (∀ W∈caps,W⊆U ∧ (W.card:ℝ)≤n*exp (6*P)) ∧
      (∀ S T,S⊆U → S.card=n → T⊆UT → T.card=t →
        (incidenceCount S T:ℝ)≤τ*(n:ℝ)*t/Nat.card K →
        ∃ W∈caps,(n:ℝ)/2≤(S∩W).card) ∧
      log ((caps.card:ℝ)+1)≤2000*(Nat.card K:ℝ)*P*
        (log ((U.card:ℝ)/n)+log ((UT.card:ℝ)/t)+P) := by
  have ht : Tendsto (fun σ : ℝ => C*σ^(-100*beta η)) atTop (𝓝 0) := by
    simpa using (tendsto_rpow_neg_atTop (by have := beta_pos hη; positivity : 0<100*beta η)).const_mul C
  filter_upwards [full_source_cover_uniform hη C hC,
    eventually_uniform_L hη (eventually_ge_atTop (2000:ℝ)),eventually_uniform_R hη 1,
    eventually_training_loss hη C 1 (by linarith) (by norm_num),
    ht.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1/20000)),
    eventually_ge_atTop (1:ℝ)] with σ hcover hL hR hbsmall ht hσ
  intro K V _ _ _ _ _ D R had hex hdim U UT n t b τ hn ht0 hnu htu hb hbu hτ hτu hprodlo hprodhi
  let P := scaleP σ η D R
  have hL' := hL D R had
  have hR' := hR D R had
  have hLP : scaleL σ η D≤P := le_mul_of_one_le_right (by linarith) hR'
  have hP : 2000≤P := hL'.trans hLP
  have hτsmall : τ≤1/20000 := hτu.trans ht.le
  have hbP : b≤P := by
    have hh := hbsmall D R had b 0 hbu (by positivity)
    simp only [mul_zero,add_zero,one_mul] at hh
    exact hh.trans hLP
  have hn' : (0:ℝ)<n := by exact_mod_cast hn
  have ht' : (0:ℝ)<t := by exact_mod_cast ht0
  have hd : 0≤log ((U.card:ℝ)/n) := log_nonneg ((le_div_iff₀ hn').mpr
    (by simpa only [one_mul] using (show (n:ℝ)≤U.card by exact_mod_cast hnu)))
  have hdT : 0≤log ((UT.card:ℝ)/t) := log_nonneg ((le_div_iff₀ ht').mpr
    (by simpa only [one_mul] using (show (t:ℝ)≤UT.card by exact_mod_cast htu)))
  by_cases hnt : n≤t
  · obtain ⟨caps,hs,hc,hl⟩ := hcover K V D R had hex hdim U n b τ hn hnu hb hbu hτ hτu
    refine ⟨caps,hs,?_,hl.trans ?_⟩
    · intro S T hSU hSn _ hTt hsp
      apply hc S
      refine ⟨hSU,hSn,T,card_pos.mp (by omega),?_,?_,?_⟩
      · rw [hSn,hTt]; exact hnt
      · rwa [hSn,hTt]
      · rwa [hSn,hTt]
    · have hq : (0:ℝ)≤Nat.card K := by positivity
      have hpos : 0≤(Nat.card K:ℝ)*P*(log ((U.card:ℝ)/n)+P) := by positivity
      have hposT : 0≤(Nat.card K:ℝ)*P*log ((UT.card:ℝ)/t) := by positivity
      nlinarith only [hpos,hposT]
  · have htn : t≤n := (le_of_not_ge hnt)
    have hdim' : Module.finrank K (Module.Dual K V)=3 := Subspace.dual_finrank_eq.trans hdim
    obtain ⟨desc,hs,hc,hl⟩ := hcover K (Module.Dual K V) D R had hex hdim' UT t b τ ht0 htu hb hbu hτ hτu
    obtain ⟨caps,hsize,hcapture,hlen⟩ := dual_description hdim U UT n t hn ht0 hnu htu
      P b τ (by linarith) hτsmall hprodhi desc hs hc hl
    refine ⟨caps,?_,?_,hlen⟩
    · intro W hW
      obtain ⟨hWU,hw⟩ := hsize W hW
      refine ⟨hWU,hw.trans ?_⟩
      have he : (Nat.card K:ℝ)^3≤(n:ℝ)*t*exp b := by
        have hh := mul_le_mul_of_nonneg_right hprodlo (exp_pos b).le
        have heq : exp (-b)*exp b=1 := by rw [←exp_add,neg_add_cancel,exp_zero]
        nlinarith only [hh,show (Nat.card K:ℝ)^3*exp (-b)*exp b=(Nat.card K:ℝ)^3 by rw [mul_assoc,heq,mul_one]]
      have hsize' : 2000*(Nat.card K:ℝ)^3/t≤2000*(n:ℝ)*exp b := by
        apply (div_le_iff₀ ht').mpr
        nlinarith only [he]
      apply hsize'.trans
      have hlog : log (2000:ℝ)≤1999 := by
        have := log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2000); linarith
      have hexp : 2000*exp b≤exp (6*P) := by
        rw [←exp_log (by norm_num : (0:ℝ)<2000),←exp_add]
        apply exp_le_exp.mpr
        linarith
      nlinarith only [mul_le_mul_of_nonneg_left hexp hn'.le]
    · intro S T hSU hSn hTU hTt hsp
      exact hcapture S T hSU hSn hTU hTt htn hprodlo hsp

end
end SharpLogRamsey.PlanarLearning

end

end OAI
