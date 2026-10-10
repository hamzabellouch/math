import Mathlib
import OAI.Combinatorics.SharpRamsey.Geometry.ProjectiveTransport
import OAI.Combinatorics.SharpRamsey.Validation.ValidationFraction

namespace OAI

section
namespace SharpLogRamsey.Validation
open Finset Real Incidence ProjectiveDuality
open scoped Classical BigOperators
noncomputable section
variable {K V : Type*} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]
local instance flat_JoinedValidationReturn_1 : Finite (Module.Dual K V) := Module.finite_of_finite K
local instance flat_JoinedValidationReturn_2 : Fintype (Projectivization K V) := by
  letI : Finite V := Module.finite_of_finite K
  exact Fintype.ofFinite _
local instance flat_JoinedValidationReturn_3 : Fintype (Projectivization K (Module.Dual K V)) := Fintype.ofFinite _
local instance flat_JoinedValidationReturn_4 : Finite (Module.Dual K (Module.Dual K V)) := Module.finite_of_finite K
local instance flat_JoinedValidationReturn_5 : Fintype (Projectivization K (Module.Dual K (Module.Dual K V))) := Fintype.ofFinite _

theorem reverse_extend {r : ℕ} (hdim : Module.finrank K V=r+3)
    (descriptions : Finset (Finset (Projectivization K (Module.Dual K V))))
    (U : Finset (Projectivization K V)) (N t : ℕ)
    (hN : 0<N) (ht : 0<t) (hNU : N≤U.card) (b : ℝ) (hb : 0≤b)
    (hsize : ∀ W∈descriptions,(W.card:ℝ)≤t*exp b)
    (hprod : (N:ℝ)*t≤2*(Nat.card K:ℝ)^(r+3)) :
    let q : ℝ := Nat.card K
    let H := ((Fintype.card (Projectivization K (Module.Dual K V)):ℝ)+
      Fintype.card (Projectivization K (Module.Dual K (Module.Dual K V))))*log 2
    let E := 2*((scheduleLength q U.card N:ℝ)*(b+log 2)+log 2+log (H+1))+log 3
    ∃ caps : Finset (Finset (Projectivization K V)),
      (∀ F∈caps,F⊆U ∧ (F.card:ℝ)≤2000*q^(r+3)/t) ∧
      (∀ S T,S⊆U → S.card=N → T.card=t →
        (incidenceCount S T:ℝ)≤(N:ℝ)*t/(20000*q) →
        (∃ W∈descriptions,(t:ℝ)/2≤(T∩W).card) →
        ∃ F∈caps,(99/100:ℝ)*N≤(S∩F).card) ∧
      log ((caps.card:ℝ)+1)≤log ((descriptions.card:ℝ)+1)+E := by
  dsimp only
  let e := bidual (K:=K) (V:=V)
  have hcU : (U.image e).card=U.card := card_image_of_injective _ e.injective
  have hd : Module.finrank K (Module.Dual K V)=r+3 := Subspace.dual_finrank_eq.trans hdim
  obtain ⟨A,hAs,hAc,hAl⟩ := extend_cover_fraction hd descriptions (U.image e) t N ht hN
    (by rwa [hcU]) 2 b (by norm_num) hb hsize (by simpa [mul_comm] using hprod)
  refine ⟨A.image (fun W => W.image e.symm),?_,?_,?_⟩
  · intro W hW
    obtain ⟨F,hF,rfl⟩ := mem_image.mp hW
    obtain ⟨hFU,hcard,_⟩ := pullback_cover e U ∅ F (hAs F hF).1
    refine ⟨hFU,?_⟩
    rw [hcard]
    simpa only [show (1000:ℝ)*2=2000 by norm_num] using (hAs F hF).2
  · intro S T hSU hSN hTt hsp hcap
    have hinc : incidenceCount T (S.image e)=incidenceCount S T := incidenceCount_bidual S T
    have hcS : (S.image e).card=N := (card_image_of_injective _ e.injective).trans hSN
    have hsp' : (incidenceCount T (S.image e):ℝ)≤(t:ℝ)*N/(10000*2*Nat.card K) := by
      rw [hinc]
      convert hsp using 1 ; ring
    obtain ⟨F,hF,hcapture⟩ := hAc T (S.image e) hTt (image_subset_image hSU) hcS hsp' hcap
    refine ⟨F.image e.symm,mem_image.mpr ⟨F,hF,rfl⟩,?_⟩
    rw [(pullback_cover e U S F (hAs F hF).1).2.2]
    exact hcapture
  · have hc : ((A.image (fun W => W.image e.symm)).card:ℝ)≤A.card := by
      exact_mod_cast card_image_le (s:=A) (f:=fun W => W.image e.symm)
    have hl : log (((A.image (fun W => W.image e.symm)).card:ℝ)+1)≤log ((A.card:ℝ)+1) :=
      log_le_log (by positivity) (by linarith)
    exact hl.trans (by simpa only [hcU] using hAl)

lemma reverse_size (q N t C b : ℝ) (r : ℕ) (_hq : 0<q) (hN : 0<N) (hC : 0<C)
    (hprod : q^r*exp (-b)≤N*t) : C*q^r/N≤t*exp (b+log C) := by
  rw [exp_add,exp_log hC]
  apply (div_le_iff₀ hN).mpr
  have h := mul_le_mul_of_nonneg_right hprod (exp_pos b).le
  rw [mul_assoc,←exp_add,neg_add_cancel,exp_zero,mul_one] at h
  nlinarith only [mul_le_mul_of_nonneg_left h hC.le]

theorem return_cover {r : ℕ} (hdim : Module.finrank K V=r+3)
    (descriptions : Finset (Finset (Projectivization K V)))
    (U : Finset (Projectivization K V))
    (UT : Finset (Projectivization K (Module.Dual K V))) (N t : ℕ)
    (hN : 0<N) (ht : 0<t) (hNU : N≤U.card) (htU : t≤UT.card)
    (c B b : ℝ) (hc : 2≤c) (hB : 0≤B) (hb : 0≤b)
    (hsize : ∀ W∈descriptions,(W.card:ℝ)≤N*exp B)
    (hprod : (N:ℝ)*t≤2*(Nat.card K:ℝ)^(r+3))
    (hprodlo : (Nat.card K:ℝ)^(r+3)*exp (-b)≤(N:ℝ)*t) :
    let q : ℝ := Nat.card K
    let H := ((Fintype.card (Projectivization K V):ℝ)+
      Fintype.card (Projectivization K (Module.Dual K V)))*log 2
    let H' := ((Fintype.card (Projectivization K (Module.Dual K V)):ℝ)+
      Fintype.card (Projectivization K (Module.Dual K (Module.Dual K V))))*log 2
    let E₁ := 2*((scheduleLength q UT.card t:ℝ)*(B+log c)+log 2+log (H+1))+log 3
    let E₂ := 2*((scheduleLength q U.card N:ℝ)*(b+log (1000*c)+log 2)+log 2+log (H'+1))+log 3
    ∃ caps : Finset (Finset (Projectivization K V)),
      (∀ F∈caps,F⊆U ∧ (F.card:ℝ)≤2000*q^(r+3)/t) ∧
      (∀ S T,S⊆U → S.card=N → T⊆UT → T.card=t →
        (incidenceCount S T:ℝ)≤(N:ℝ)*t/(10000*c*q) →
        (∃ W∈descriptions,(N:ℝ)/c≤(S∩W).card) →
        ∃ F∈caps,(99/100:ℝ)*N≤(S∩F).card) ∧
      log ((caps.card:ℝ)+1)≤log ((descriptions.card:ℝ)+1)+E₁+E₂ := by
  dsimp only
  obtain ⟨A,hAs,hAc,hAl⟩ := extend_cover_fraction hdim descriptions UT N t hN ht htU c B
    (by linarith) hB hsize hprod
  have hq : (0:ℝ)<Nat.card K := by exact_mod_cast Nat.card_pos (α:=K)
  have hn : (0:ℝ)<N := by exact_mod_cast hN
  have hc0 : 0<c := by linarith
  have hsA (W) (hW : W∈A) : (W.card:ℝ)≤t*exp (b+log (1000*c)) :=
    (hAs W hW).2.trans (reverse_size (Nat.card K) N t (1000*c) b (r+3) hq hn (by positivity) hprodlo)
  obtain ⟨F,hFs,hFc,hFl⟩ := reverse_extend hdim A U N t hN ht hNU (b+log (1000*c))
    (add_nonneg hb (log_nonneg (by linarith))) hsA hprod
  refine ⟨F,hFs,?_,hFl.trans (by linarith only [hAl])⟩
  intro S T hSU hSN hTU hTt hsp hcap
  obtain ⟨W,hW,hcapture⟩ := hAc S T hSN hTU hTt hsp hcap
  apply hFc S T hSU hSN hTt _ ⟨W,hW,by linarith⟩
  apply hsp.trans
  apply div_le_div_of_nonneg_left (by positivity) (by positivity)
  nlinarith

end
end SharpLogRamsey.Validation

end

end OAI
