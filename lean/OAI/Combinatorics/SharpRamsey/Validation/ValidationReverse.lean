import Mathlib
import OAI.Combinatorics.SharpRamsey.Validation.ValidationReturn

namespace OAI

section
namespace SharpLogRamsey.Validation
open Finset Real Incidence ProjectiveDuality
open scoped Classical BigOperators
noncomputable section
variable {K V : Type*} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]
local instance flat_JoinedValidationReverse_1 : Finite (Module.Dual K V) := Module.finite_of_finite K
local instance flat_JoinedValidationReverse_2 : Fintype (Projectivization K V) := by
  letI : Finite V := Module.finite_of_finite K
  exact Fintype.ofFinite _
local instance flat_JoinedValidationReverse_3 : Fintype (Projectivization K (Module.Dual K V)) := Fintype.ofFinite _
local instance flat_JoinedValidationReverse_4 : Finite (Module.Dual K (Module.Dual K V)) := Module.finite_of_finite K
local instance flat_JoinedValidationReverse_5 : Fintype (Projectivization K (Module.Dual K (Module.Dual K V))) := Fintype.ofFinite _

theorem reverse_extend_fraction {r : ℕ} (hdim : Module.finrank K V=r+3)
    (descriptions : Finset (Finset (Projectivization K (Module.Dual K V))))
    (U : Finset (Projectivization K V)) (N t : ℕ)
    (hN : 0<N) (ht : 0<t) (hNU : N≤U.card) (c b : ℝ) (hc : 1≤c) (hb : 0≤b)
    (hsize : ∀ W∈descriptions,(W.card:ℝ)≤t*exp b)
    (hprod : (N:ℝ)*t≤2*(Nat.card K:ℝ)^(r+3)) :
    let q : ℝ := Nat.card K
    let H := ((Fintype.card (Projectivization K (Module.Dual K V)):ℝ)+
      Fintype.card (Projectivization K (Module.Dual K (Module.Dual K V))))*log 2
    let E := 2*((scheduleLength q U.card N:ℝ)*(b+log c)+log 2+log (H+1))+log 3
    ∃ caps : Finset (Finset (Projectivization K V)),
      (∀ F∈caps,F⊆U ∧ (F.card:ℝ)≤(1000*c)*q^(r+3)/t) ∧
      (∀ S T,S⊆U → S.card=N → T.card=t →
        (incidenceCount S T:ℝ)≤(N:ℝ)*t/(10000*c*q) →
        (∃ W∈descriptions,(t:ℝ)/c≤(T∩W).card) →
        ∃ F∈caps,(99/100:ℝ)*N≤(S∩F).card) ∧
      log ((caps.card:ℝ)+1)≤log ((descriptions.card:ℝ)+1)+E := by
  dsimp only
  let e := bidual (K:=K) (V:=V)
  have hcU : (U.image e).card=U.card := card_image_of_injective _ e.injective
  have hd : Module.finrank K (Module.Dual K V)=r+3 := Subspace.dual_finrank_eq.trans hdim
  obtain ⟨A,hAs,hAc,hAl⟩ := extend_cover_fraction hd descriptions (U.image e) t N ht hN
    (by rwa [hcU]) c b hc hb hsize (by simpa [mul_comm] using hprod)
  refine ⟨A.image (fun W => W.image e.symm),?_,?_,?_⟩
  · intro W hW
    obtain ⟨F,hF,rfl⟩ := mem_image.mp hW
    obtain ⟨hFU,hcard,_⟩ := pullback_cover e U ∅ F (hAs F hF).1
    refine ⟨hFU,?_⟩
    rw [hcard]
    exact (hAs F hF).2
  · intro S T hSU hSN hTt hsp hcap
    have hinc : incidenceCount T (S.image e)=incidenceCount S T := incidenceCount_bidual S T
    have hcS : (S.image e).card=N := (card_image_of_injective _ e.injective).trans hSN
    have hsp' : (incidenceCount T (S.image e):ℝ)≤(t:ℝ)*N/(10000*c*Nat.card K) := by
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

end
end SharpLogRamsey.Validation

end

end OAI
