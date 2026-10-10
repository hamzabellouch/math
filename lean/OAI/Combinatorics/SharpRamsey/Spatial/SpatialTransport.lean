import Mathlib
import OAI.Combinatorics.SharpRamsey.Spatial.SpatialComplete

namespace OAI

section
namespace SharpLogRamsey.SpatialPublic
open Finset Real Filter SourceScales Incidence ProjectiveDuality
open scoped Classical Topology
noncomputable section

theorem complete_cover_any {η : ℝ} (hη : 0<η) (C : ℝ) (hC : 1≤C) :
    ∀ᶠ σ : ℝ in atTop,∀ (q : ℕ) [Fact q.Prime],3≤q → exp σ=(q:ℝ) →
    ∀ (V : Type) [AddCommGroup V] [Module (ZMod q) V] [FiniteDimensional (ZMod q) V],
    Module.finrank (ZMod q) V=4 → ∀ D R,Admissible σ η D R →
    ∀ (U : Finset (Projectivization (ZMod q) V))
      (UT : Finset (Projectivization (ZMod q) (Module.Dual (ZMod q) V)))
      (n t : ℕ) (b τ : ℝ),
    0<n → 0<t → n≤U.card → t≤UT.card → n≤t → (n:ℝ)≤2*(q:ℝ)^2 →
    0≤b → b≤C*scaleKstar σ η D → 0<τ → τ≤C*σ^(-100*beta η) →
    let P := scaleP σ η D R
    ∃ caps : Finset (Finset (Projectivization (ZMod q) V)),
      (∀ W∈caps,W⊆U ∧ (W.card:ℝ)≤n*exp (6*P)) ∧
      (∀ S T,S⊆U → S.card=n → T⊆UT → T.card=t →
        (q:ℝ)^4*exp (-b)≤(n:ℝ)*t → (incidenceCount S T:ℝ)≤τ*(n:ℝ)*t/q →
        ∃ W∈caps,(n:ℝ)/100≤(S∩W).card) ∧
      log ((caps.card:ℝ)+1)≤5000*(q:ℝ)*P*
        (log ((U.card:ℝ)/n)+log ((UT.card:ℝ)/t)+P) := by
  filter_upwards [complete_cover hη C hC] with σ hs
  intro q _ hq hex V _ _ _ hd D R had U UT n t b τ hn ht hnu htu hnt hnup hb hbu hτ hτu
  let e : V ≃ₗ[ZMod q] (Fin 4 → ZMod q) := LinearEquiv.ofFinrankEq _ _ (by simpa using hd)
  let f := mapEquiv e
  let g := mapEquiv e.symm.dualMap
  have hcU : (U.image f).card=U.card := card_image_of_injective _ f.injective
  have hcT : (UT.image g).card=UT.card := card_image_of_injective _ g.injective
  obtain ⟨A,hAs,hAc,hAl⟩ := hs q hq hex D R had (U.image f) (UT.image g) n t b τ
    hn ht (by simpa only [hcU] using hnu) (by simpa only [hcT] using htu) hnt hnup hb hbu hτ hτu
  refine ⟨A.image (fun W => W.image f.symm),?_,?_,?_⟩
  · intro W hW
    obtain ⟨W₀,hW₀,rfl⟩ := mem_image.mp hW
    obtain ⟨hsub,hcard,_⟩ := pullback_cover f U U W₀ (hAs W₀ hW₀).1
    exact ⟨hsub,by simpa only [hcard] using (hAs W₀ hW₀).2⟩
  · intro S T hSU hSn hTU hTt hprod hsp
    have hcS : (S.image f).card=n := by rw [card_image_of_injective _ f.injective,hSn]
    have hcT' : (T.image g).card=t := by rw [card_image_of_injective _ g.injective,hTt]
    have hsp' : (incidenceCount (S.image f) (T.image g):ℝ)≤τ*(n:ℝ)*t/q := by
      simpa only [f,g,incidenceCount_mapEquiv] using hsp
    obtain ⟨W,hW,hcap⟩ := hAc (S.image f) (T.image g)
      (image_subset_image hSU) hcS (image_subset_image hTU) hcT' hprod hsp'
    refine ⟨W.image f.symm,mem_image.mpr ⟨W,hW,rfl⟩,?_⟩
    rw [(pullback_cover f U S W (hAs W hW).1).2.2]
    exact hcap
  · have hcard : ((A.image (fun W => W.image f.symm)).card:ℝ)≤A.card := by
      exact_mod_cast card_image_le (s:=A) (f:=fun W => W.image f.symm)
    have hl : log (((A.image (fun W => W.image f.symm)).card:ℝ)+1)≤log ((A.card:ℝ)+1) :=
      log_le_log (by positivity) (by linarith only [hcard])
    exact hl.trans (by simpa only [hcU,hcT] using hAl)

end
end SharpLogRamsey.SpatialPublic

end

end OAI
