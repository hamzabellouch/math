import Mathlib
import OAI.Combinatorics.SharpRamsey.Planar.PlanarUniform
import OAI.Combinatorics.SharpRamsey.Validation.ValidationExtend
import OAI.Combinatorics.SharpRamsey.Geometry.ProjectiveTransport

namespace OAI

section
namespace SharpLogRamsey.PlanarLearning
open Finset Real Filter SourceScales Incidence
open scoped Classical BigOperators Topology NNReal
noncomputable section
local instance flat_JoinedPlanarBoth_1 {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] : Finite (Module.Dual K V) := Module.finite_of_finite K
local instance flat_JoinedPlanarBoth_2 {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] : Fintype (Projectivization K V) := by
  letI : Finite V := Module.finite_of_finite K
  exact Fintype.ofFinite _

lemma validation_description_cost {q P d H : ℝ} (hq : 1≤q) (hP : 1≤P)
    (hd : 0≤d) (hH : log (H+1)≤4*q) (h : ℕ) (hh : (h:ℝ)≤20*q*(d+2)+1) :
    2*((h:ℝ)*(6*P+log 2)+log 2+log (H+1))+log 3≤1000*q*P*(d+P) := by
  have hl2 : 0≤log (2:ℝ) := log_nonneg (by norm_num)
  have hl2' : log (2:ℝ)≤1 := by have := log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2); linarith
  have hl3 : log (3:ℝ)≤2 := by have := log_le_sub_one_of_pos (by norm_num : (0:ℝ)<3); linarith
  have hh' : (h:ℝ)≤21*q*(d+2) := by nlinarith
  have h1 := mul_le_mul_of_nonneg_right hh' (show 0≤6*P+log 2 by positivity)
  have h2 := mul_le_mul_of_nonneg_left (show 6*P+log 2≤7*P by linarith)
    (show 0≤21*q*(d+2) by positivity)
  have hqP : q≤q*P := le_mul_of_one_le_right (by linarith) hP
  have hPP : q*P≤q*P*P := le_mul_of_one_le_right (by positivity) hP
  have hqp : 1≤q*P := one_le_mul_of_one_le_of_one_le hq hP
  have hpos : 0≤q*P*d := by positivity
  nlinarith

variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

lemma plane_pair_log_card (hdim : Module.finrank K V=3) :
    log (((Fintype.card (Projectivization K V):ℝ)+
      Fintype.card (Projectivization K (Module.Dual K V)))*log 2+1)≤4*Nat.card K := by
  let A : ℝ := Fintype.card (Projectivization K V)
  let B : ℝ := Fintype.card (Projectivization K (Module.Dual K V))
  have ha : 0≤A := by positivity
  have hb : 0≤B := by positivity
  have hl2 : 0≤log (2:ℝ) := log_nonneg (by norm_num)
  have hl2' : log (2:ℝ)≤1 := by have := log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2); linarith
  have hbound : (A+B)*log 2+1≤(A+1)*(B+1) := by nlinarith [mul_nonneg ha hb]
  have hh := log_le_log (by positivity : 0<(A+B)*log 2+1) hbound
  rw [log_mul (by positivity) (by positivity)] at hh
  have hA := (plane_log_card hdim).1
  have hB := (plane_log_card (K:=K) (V:=Module.Dual K V) (Subspace.dual_finrank_eq.trans hdim)).1
  change log ((A+B)*log 2+1)≤_
  dsimp only [A,B] at hh
  linarith

theorem dual_description
    (hdim : Module.finrank K V=3) (U : Finset (Projectivization K V))
    (UT : Finset (Projectivization K (Module.Dual K V))) (n t : ℕ)
    (hn : 0<n) (ht : 0<t) (hnu : n≤U.card) (htu : t≤UT.card)
    (P b τ : ℝ) (hP : 1≤P) (hτ : τ≤1/20000)
    (hprod : (n:ℝ)*t≤2*(Nat.card K:ℝ)^3)
    (descriptions : Finset (Finset (Projectivization K (Module.Dual K V))))
    (hsize : ∀ W∈descriptions,W⊆UT ∧ (W.card:ℝ)≤t*exp (6*P))
    (hcapture : ∀ T,Input UT t b τ T → ∃ W∈descriptions,(t:ℝ)/2≤(T∩W).card)
    (hlen : log ((descriptions.card:ℝ)+1)≤200*(Nat.card K:ℝ)*P*(log ((UT.card:ℝ)/t)+P)) :
    ∃ caps : Finset (Finset (Projectivization K V)),
      (∀ W∈caps,W⊆U ∧ (W.card:ℝ)≤2000*(Nat.card K:ℝ)^3/t) ∧
      (∀ S T,S⊆U → S.card=n → T⊆UT → T.card=t → t≤n →
        (Nat.card K:ℝ)^3*exp (-b)≤(n:ℝ)*t →
        (incidenceCount S T:ℝ)≤τ*(n:ℝ)*t/Nat.card K →
        ∃ W∈caps,(n:ℝ)/2≤(S∩W).card) ∧
      log ((caps.card:ℝ)+1)≤2000*(Nat.card K:ℝ)*P*
        (log ((U.card:ℝ)/n)+log ((UT.card:ℝ)/t)+P) := by
  let e := ProjectiveDuality.bidual (K:=K) (V:=V)
  have hcard : (U.image e).card=U.card := card_image_of_injective _ e.injective
  have hdim' : Module.finrank K (Module.Dual K V)=0+3 := Subspace.dual_finrank_eq.trans hdim
  obtain ⟨caps,hs,hc,hl⟩ := Validation.extend_cover hdim' descriptions (U.image e) t n ht hn
    (by rwa [hcard]) (6*P) (by linarith) (fun W hW => (hsize W hW).2)
    (by simpa only [Nat.zero_add,mul_comm] using hprod)
  let out := caps.image (fun W => W.image e.symm)
  have hq : (1:ℝ)≤Nat.card K := by exact_mod_cast (show 1≤Nat.card K from Nat.card_pos (α:=K))
  have hn' : (0:ℝ)<n := by exact_mod_cast hn
  have ht' : (0:ℝ)<t := by exact_mod_cast ht
  have hd : 0≤log ((U.card:ℝ)/n) := log_nonneg ((le_div_iff₀ hn').mpr (by simpa only [one_mul] using (show (n:ℝ)≤U.card by exact_mod_cast hnu)))
  have hdT : 0≤log ((UT.card:ℝ)/t) := log_nonneg ((le_div_iff₀ ht').mpr (by simpa only [one_mul] using (show (t:ℝ)≤UT.card by exact_mod_cast htu)))
  refine ⟨out,?_,?_,?_⟩
  · intro W hW
    obtain ⟨F,hF,rfl⟩ := mem_image.mp hW
    obtain ⟨hFU,hsizeF⟩ := hs F hF
    have hp := ProjectiveDuality.pullback_cover e U ∅ F hFU
    exact ⟨hp.1,by rw [hp.2.1]; exact hsizeF⟩
  · intro S T hSU hSn hTU hTt htn hprodlo hsp
    have hS : S.Nonempty := card_pos.mp (by omega)
    have hinc : incidenceCount T (S.image e)=incidenceCount S T :=
      ProjectiveDuality.incidenceCount_bidual S T
    have hcS : (S.image e).card=n := (card_image_of_injective _ e.injective).trans hSn
    have hin : Input UT t b τ T := by
      refine ⟨hTU,hTt,S.image e,hS.image _,?_,?_,?_⟩
      · rw [hTt,hcS]; exact htn
      · rw [hTt,hcS]; nlinarith only [hprodlo]
      · rw [hinc,hTt,hcS]
        convert hsp using 1
        ring
    obtain ⟨W,hW,hcap⟩ := hcapture T hin
    have hsp' : (incidenceCount T (S.image e):ℝ)≤(t:ℝ)*n/(20000*Nat.card K) := by
      rw [hinc]
      apply hsp.trans
      have hh := mul_le_mul_of_nonneg_right hτ (show 0≤(n:ℝ)*t/(Nat.card K:ℝ) by positivity)
      convert hh using 1 <;> ring
    obtain ⟨F,hF,hcapF⟩ := hc T (S.image e) hTt (image_subset_image hSU) hcS hsp' ⟨W,hW,hcap⟩
    obtain ⟨hFU,_⟩ := hs F hF
    have hp := ProjectiveDuality.pullback_cover e U S F hFU
    refine ⟨F.image e.symm,mem_image.mpr ⟨F,hF,rfl⟩,?_⟩
    rw [hp.2.2]
    nlinarith
  · have hbound := hl
    rw [hcard] at hbound
    have hh : (Validation.scheduleLength (Nat.card K) U.card n:ℝ)≤
        20*(Nat.card K:ℝ)*(log ((U.card:ℝ)/n)+2)+1 := by
      exact (Nat.ceil_lt_add_one (by positivity)).le
    have hcost := validation_description_cost hq hP hd
      (plane_pair_log_card (K:=K) (V:=Module.Dual K V) hdim')
      (Validation.scheduleLength (Nat.card K) U.card n) hh
    have hc' : (out.card:ℝ)≤caps.card := by exact_mod_cast card_image_le (s:=caps) (f:=fun W => W.image e.symm)
    have hout : log ((out.card:ℝ)+1)≤log ((caps.card:ℝ)+1) := log_le_log (by positivity) (by linarith)
    apply hout.trans (hbound.trans _)
    have hpos1 : 0≤(Nat.card K:ℝ)*P*log ((U.card:ℝ)/n) := by positivity
    have hpos2 : 0≤(Nat.card K:ℝ)*P*log ((UT.card:ℝ)/t) := by positivity
    have hpositive : 0≤(Nat.card K:ℝ)*P^2 := by positivity
    nlinarith only [hlen,hcost,hpos1,hpos2,hpositive]

end
end SharpLogRamsey.PlanarLearning

end

end OAI
