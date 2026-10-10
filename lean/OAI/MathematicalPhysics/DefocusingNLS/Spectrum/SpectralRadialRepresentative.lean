import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralRadialVolumeWeak
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

namespace OAI

/-! The positive-radius representative of every completed radial H¹ vector. -/

open Set MeasureTheory Filter Topology
open scoped SchwartzMap
namespace DefocusingNLS

noncomputable def spectralRadialRepresentative (R : ℝ) (hR : 0 < R)
    (u : SpectralRadialEnergy R) (r : ℝ) : ℂ :=
  if hr : 0 < r then spectralRadialPointValue R hR r hr u else 0

theorem spectralRadialSmoothApproximation (R : ℝ) (u : SpectralRadialEnergy R) :
    ∃ f : ℕ → 𝓢(ℝ,ℂ),
      Tendsto (fun n => spectralRadialSmoothEmbedding R (f n)) atTop (𝓝 u) := by
  obtain ⟨v,hv,ht⟩ := mem_closure_iff_seq_limit.mp ((spectralRadialSmoothEmbedding_dense R) u)
  choose f hf using hv
  refine ⟨f,?_⟩
  simpa only [hf] using ht

theorem spectralRadialRepresentative_smooth (R : ℝ) (hR : 0 < R) (f : 𝓢(ℝ,ℂ))
    (r : ℝ) (hr : 0 < r) (hrR : r ≤ R) :
    spectralRadialRepresentative R hR (spectralRadialSmoothEmbedding R f) r=f r := by
  rw [spectralRadialRepresentative,dite_eq_left hr,spectralRadialPointValue_smooth R hR r hr hrR]

theorem spectralRadialRepresentative_ae (R : ℝ) (hR : 0 < R) (u : SpectralRadialEnergy R) :
    spectralRadialRepresentative R hR u =ᵐ[radialPressureMeasure R] spectralRadialValue R u := by
  obtain ⟨f,hf⟩ := spectralRadialSmoothApproximation R u
  have hv : Tendsto (fun n => spectralRadialSmoothValue R (f n)) atTop
      (𝓝 (spectralRadialValue R u)) := by
    simpa only [Function.comp_def,spectralRadialSmoothEmbedding_value] using
      (spectralRadialValue R).continuous.continuousAt.tendsto.comp hf
  obtain ⟨φ,hφ,hae⟩ := (tendstoInMeasure_of_tendsto_Lp hv).exists_seq_tendsto_ae
  have hall : ∀ᵐ r ∂radialPressureMeasure R,
      ∀ n, spectralRadialSmoothValue R (f (φ n)) r=f (φ n) r :=
    ae_all_iff.mpr (fun n => spectralRadialSmoothValue_ae R (f (φ n)))
  filter_upwards [hae,hall,radialPressureMeasure_ae_positive R] with r hr hfr hrpos
  have he := ((spectralRadialPointValue R hR r hrpos.1).continuous.continuousAt.tendsto.comp hf).comp
    hφ.tendsto_atTop
  have he' : Tendsto (fun n => f (φ n) r) atTop
      (𝓝 (spectralRadialRepresentative R hR u r)) := by
    simpa only [Function.comp_def,spectralRadialPointValue_smooth R hR r hrpos.1 hrpos.2,
      spectralRadialRepresentative,dite_eq_left hrpos.1] using he
  have hr' : Tendsto (fun n => f (φ n) r) atTop (𝓝 (spectralRadialValue R u r)) := by
    simpa only [hfr] using hr
  exact tendsto_nhds_unique he' hr'

end DefocusingNLS

end OAI
