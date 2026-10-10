import OAI.Probability.ClassicalON.UpperEndpoint

namespace OAI

universe uV

noncomputable section
open MeasureTheory Set
open scoped BigOperators Topology Classical
namespace ClassicalON

variable {V : Type uV} [Fintype V]

def glueAmplitude (B : Set V) (a : B → Amplitude) (r : ↥(Bᶜ) → Amplitude) : V → Amplitude :=
  (MeasurableEquiv.piEquivPiSubtypeProd (fun _ : V => Amplitude) (·∈B)).symm (a,r)

omit [Fintype V] in
theorem continuous_glueAmplitude (B : Set V) :
    Continuous (fun p : (B → Amplitude)×(↥(Bᶜ) → Amplitude) => glueAmplitude B p.1 p.2) :=
  (Homeomorph.piEquivPiSubtypeProd (·∈B) (fun _ : V => Amplitude)).symm.continuous

omit [Fintype V] in
@[simp] theorem glueAmplitude_in (B : Set V) (a : B → Amplitude) (r : ↥(Bᶜ) → Amplitude)
    (v : B) : glueAmplitude B a r v=a v := by
  simp [glueAmplitude,MeasurableEquiv.piEquivPiSubtypeProd,Equiv.piEquivPiSubtypeProd,v.property]

omit [Fintype V] in
@[simp] theorem glueAmplitude_out (B : Set V) (a : B → Amplitude) (r : ↥(Bᶜ) → Amplitude)
    (v : ↥(Bᶜ)) : glueAmplitude B a r v=r v := by
  simp [glueAmplitude,MeasurableEquiv.piEquivPiSubtypeProd,Equiv.piEquivPiSubtypeProd,show v.val∉B from v.property]

theorem integral_amplitude_split (μ : Measure Amplitude) [IsProbabilityMeasure μ]
    (B : Set V) (F : (V → Amplitude) → ℝ) (hF : Continuous F) :
    (∫ r,F r ∂Measure.pi (fun _ : V => μ))=
      ∫ a,∫ r,F (glueAmplitude B a r) ∂Measure.pi (fun _ : ↥(Bᶜ) => μ)
        ∂Measure.pi (fun _ : B => μ) := by
  let e := MeasurableEquiv.piEquivPiSubtypeProd (fun _ : V => Amplitude) (·∈B)
  have hp := (measurePreserving_piEquivPiSubtypeProd (fun _ : V => μ) (·∈B)).symm e
  rw [← hp.map_eq,integral_map hp.measurable.aemeasurable hF.aestronglyMeasurable]
  exact integral_prod _ (compact_integrable (hF.comp (continuous_glueAmplitude B)))

theorem pinEndpoint_nonneg (μ : Measure Amplitude) [IsProbabilityMeasure μ]
    [μ.IsOpenPosMeasure] (B : Set V) {F : (V → Amplitude) → ℝ} (hF : Continuous F)
    (ht : ∀ h : (B → Amplitude) → ℝ,Continuous h → (∀ a,0≤h a) → Monotone h →
      0≤∫ r,h (fun v : B => r v)*F r ∂Measure.pi (fun _ : V => μ)) :
    0≤∫ r,F (glueAmplitude B ⊤ r) ∂Measure.pi (fun _ : ↥(Bᶜ) => μ) := by
  have hc : Continuous (fun a => ∫ r,F (glueAmplitude B a r) ∂Measure.pi (fun _ : ↥(Bᶜ) => μ)) :=
    compact_parametric_integral _ (hF.comp (continuous_glueAmplitude B))
  apply upperEndpoint_nonneg (Measure.pi (fun _ : B => μ)) hc
  intro h hh hn hm
  have hh' : Continuous (fun r : V → Amplitude => h (fun v : B => r v)) := by
    apply hh.comp
    exact continuous_pi (fun v => continuous_apply v.val)
  have hs := integral_amplitude_split μ B (fun r => h (fun v : B => r v)*F r) (hh'.mul hF)
  have he : (fun a => ∫ r,h (fun v : B => glueAmplitude B a r v)*F (glueAmplitude B a r)
      ∂Measure.pi (fun _ : ↥(Bᶜ) => μ))=
      (fun a => h a*(∫ r,F (glueAmplitude B a r) ∂Measure.pi (fun _ : ↥(Bᶜ) => μ))) := by
    funext a
    simp only [glueAmplitude_in]
    exact integral_const_mul _ _
  rw [he] at hs
  rw [← hs]
  exact ht h hh hn hm

end ClassicalON

end

end OAI
