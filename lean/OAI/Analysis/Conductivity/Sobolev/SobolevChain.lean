import Mathlib
import OAI.Analysis.Conductivity.Sobolev.NonlinearLp

namespace OAI

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology

variable {g dg : ℝ → ℝ} (hg : ContDiff ℝ (↑(⊤ : ℕ∞)) g) (hdg : Continuous dg)
  (hderiv : ∀ r, HasDerivAt g (dg r) r) {C : ℝ} (hC : 0≤C)
  (hgb : ∀ r, ‖g r‖≤C*‖r‖) (hdgb : ∀ r, ‖dg r‖≤C)

def sobolevChainLp : JetSpace → JetSpace :=
  nonlinearLp ballMeasure (jetSuperposition g dg)
    (jetSuperposition_continuous hg.continuous hdg) (jetSuperpositionBound C)
    (jetSuperpositionBound_nonneg hC) (jetSuperposition_bound hC hgb hdgb)

lemma sobolevChainLp_continuous : Continuous (sobolevChainLp hg hdg hC hgb hdgb) :=
  nonlinearLp_continuous _ _ _ _ _ _

lemma sobolevChainLp_coe_ae (z : JetSpace) :
    sobolevChainLp hg hdg hC hgb hdgb z =ᵐ[ballMeasure]
      fun x => jetSuperposition g dg (z x) := nonlinearLp_coe_ae _ _ _ _ _ _ _

include hderiv

lemma sobolevChainLp_smooth {f : R3 → ℝ} (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f)
    (hm : MemLp (smoothJet f) 2 ballMeasure) :
    ∃ hgm : MemLp (smoothJet (g ∘ f)) 2 ballMeasure,
      sobolevChainLp hg hdg hC hgb hdgb (hm.toLp _) = hgm.toLp _ := by
  have he : sobolevChainLp hg hdg hC hgb hdgb (hm.toLp _) =ᵐ[ballMeasure]
      smoothJet (g ∘ f) := by
    filter_upwards [sobolevChainLp_coe_ae hg hdg hC hgb hdgb (hm.toLp _),hm.coeFn_toLp] with x hx hy
    rw [hx,hy,←smoothJet_comp hderiv (hf.differentiable (by simp))]
  have hgm := MemLp.ae_eq he (Lp.memLp (sobolevChainLp hg hdg hC hgb hdgb (hm.toLp _)))
  refine ⟨hgm,?_⟩
  apply Lp.ext
  exact he.trans hgm.coeFn_toLp.symm

lemma sobolevChainLp_preserves_H1 {z : JetSpace} (hz : z∈H1Space) :
    sobolevChainLp hg hdg hC hgb hdgb z ∈ H1Space := by
  change z ∈ (H1Space : Set JetSpace) at hz
  change _ ∈ (H1Space : Set JetSpace)
  rw [H1Space_eq_closure] at hz ⊢
  apply nonlinear_closure_preservation (sobolevChainLp_continuous hg hdg hC hgb hdgb) _ hz
  rintro w ⟨f,hf,hm,rfl⟩
  obtain ⟨hgm,he⟩ := sobolevChainLp_smooth hg hdg hderiv hC hgb hdgb hf hm
  exact ⟨g ∘ f,hg.comp hf,hgm,he⟩

lemma sobolevChainLp_preserves_H10 (hg0 : g 0=0) {z : JetSpace} (hz : z∈zeroTraceAmbient) :
    sobolevChainLp hg hdg hC hgb hdgb z ∈ zeroTraceAmbient := by
  change z ∈ (zeroTraceAmbient : Set JetSpace) at hz
  change _ ∈ (zeroTraceAmbient : Set JetSpace)
  rw [zeroTraceAmbient_eq_closure] at hz ⊢
  apply nonlinear_closure_preservation (sobolevChainLp_continuous hg hdg hC hgb hdgb) _ hz
  rintro w ⟨f,hf,hfc,hfs,hm,rfl⟩
  obtain ⟨hgm,he⟩ := sobolevChainLp_smooth hg hdg hderiv hC hgb hdgb hf hm
  refine ⟨g ∘ f,hg.comp hf,hfc.comp_left hg0,?_,hgm,he⟩
  exact (closure_mono (Function.support_comp_subset hg0 f)).trans hfs

def sobolevChain (u : H1) : H1 :=
  ⟨sobolevChainLp hg hdg hC hgb hdgb u.val,
    sobolevChainLp_preserves_H1 hg hdg hderiv hC hgb hdgb u.property⟩

lemma sobolevChain_value (u : H1) :
    (fun x => jetValue ((sobolevChain hg hdg hderiv hC hgb hdgb u).val x)) =ᵐ[ballMeasure]
      fun x => g (jetValue (u.val x)) := by
  filter_upwards [sobolevChainLp_coe_ae hg hdg hC hgb hdgb u.val] with x hx
  change jetValue (sobolevChainLp hg hdg hC hgb hdgb u.val x) = _
  rw [hx]
  change g (jetValue (u.val x))+0=g (jetValue (u.val x))
  simp

lemma sobolevChain_gradient (u : H1) :
    weakGradient (sobolevChain hg hdg hderiv hC hgb hdgb u) =ᵐ[ballMeasure]
      fun x => dg (jetValue (u.val x)) • weakGradient u x := by
  filter_upwards [sobolevChainLp_coe_ae hg hdg hC hgb hdgb u.val] with x hx
  change jetGradient (sobolevChainLp hg hdg hC hgb hdgb u.val x)=_
  rw [hx]
  ext i
  change 0+(dg (jetValue (u.val x)) • weakGradient u x) i=_
  simp

lemma sobolevChain_H10 (hg0 : g 0=0) {u : H1} (hu : u∈H10) :
    sobolevChain hg hdg hderiv hC hgb hdgb u∈H10 :=
  sobolevChainLp_preserves_H10 hg hdg hderiv hC hgb hdgb hg0 hu

end ScalarConductivity

end

end OAI
