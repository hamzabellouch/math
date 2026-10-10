import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralHarmonicForm
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralRadialRepresentative
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralRadialCoreTrace

namespace OAI

/-! Compatibility of the radial and angular coordinates after harmonic completion. -/

open Set MeasureTheory Filter Topology
open scoped SchwartzMap
namespace DefocusingNLS

theorem spectralHarmonicSmooth_dense (ell : ℕ) (R : ℝ) :
    DenseRange (spectralHarmonicSmoothEmbedding ell R) := by
  let j := spectralSmoothHarmonicJet ell R
  let f : 𝓢(ℝ,ℂ) → closure (range j) := inclusion subset_closure ∘ rangeFactorization j
  have h : DenseRange f :=
    ((denseRange_inclusion_iff subset_closure).2 subset_rfl).comp
      rangeFactorization_surjective.denseRange (continuous_inclusion subset_closure)
  exact h

theorem spectralAngularMeasure_absolutelyContinuous (R : ℝ) :
    spectralAngularMeasure R ≪ radialPressureMeasure R :=
  (withDensity_absolutelyContinuous _ _).trans (spectralRadialVolume_absolutelyContinuous R)

theorem spectralHarmonicAngularValue_ae (ell : ℕ) (R : ℝ) (u : SpectralHarmonicEnergy ell R) :
    spectralHarmonicAngularValue ell R u =ᵐ[spectralAngularMeasure R]
      fun r => (Real.sqrt ((ell : ℝ)*(ell+10)) : ℂ)*spectralHarmonicValue ell R u r := by
  obtain ⟨v,hv,ht⟩ := mem_closure_iff_seq_limit.mp ((spectralHarmonicSmooth_dense ell R) u)
  choose f hf using hv
  have ht' : Tendsto (fun n => spectralHarmonicSmoothEmbedding ell R (f n)) atTop (𝓝 u) := by
    simpa only [hf] using ht
  have hV : Tendsto (fun n => spectralRadialSmoothValue R (f n)) atTop
      (𝓝 (spectralHarmonicValue ell R u)) := by
    exact (spectralHarmonicValue ell R).continuous.continuousAt.tendsto.comp ht'
  obtain ⟨φ,hφ,hVa⟩ := (tendstoInMeasure_of_tendsto_Lp hV).exists_seq_tendsto_ae
  have hG : Tendsto (fun n => spectralHarmonicAngularValue ell R
      (spectralHarmonicSmoothEmbedding ell R (f (φ n)))) atTop
      (𝓝 (spectralHarmonicAngularValue ell R u)) :=
    ((spectralHarmonicAngularValue ell R).continuous.continuousAt.tendsto.comp ht').comp
      hφ.tendsto_atTop
  obtain ⟨ψ,hψ,hGa⟩ := (tendstoInMeasure_of_tendsto_Lp hG).exists_seq_tendsto_ae
  have hVs : ∀ᵐ r ∂radialPressureMeasure R,
      ∀ n, spectralRadialSmoothValue R (f (φ (ψ n))) r=f (φ (ψ n)) r :=
    ae_all_iff.mpr (fun n => spectralRadialSmoothValue_ae R (f (φ (ψ n))))
  have hGs : ∀ᵐ r ∂spectralAngularMeasure R, ∀ n,
      spectralHarmonicAngularValue ell R (spectralHarmonicSmoothEmbedding ell R
        (f (φ (ψ n)))) r=(Real.sqrt ((ell : ℝ)*(ell+10)) : ℂ)*f (φ (ψ n)) r := by
    apply ae_all_iff.mpr
    intro n
    rw [spectralHarmonicAngularValue_smooth]
    filter_upwards [Lp.coeFn_smul (Real.sqrt ((ell : ℝ)*(ell+10)) : ℂ)
        (spectralSmoothAngularValue R (f (φ (ψ n)))),
      BoundedContinuousFunction.coeFn_toLp 2 (spectralAngularMeasure R) ℂ
        (SchwartzMap.toBoundedContinuousFunctionCLM ℂ ℝ ℂ (f (φ (ψ n))))]
      with r hs hv
    rw [hs,Pi.smul_apply]
    change (Real.sqrt ((ell : ℝ)*(ell+10)) : ℂ)*
      spectralSmoothAngularValue R (f (φ (ψ n))) r=_
    change spectralSmoothAngularValue R (f (φ (ψ n))) r=f (φ (ψ n)) r at hv
    rw [hv]
  have hVc := (spectralAngularMeasure_absolutelyContinuous R).ae_le hVa
  have hVsc := (spectralAngularMeasure_absolutelyContinuous R).ae_le hVs
  filter_upwards [hGa,hGs,hVc,hVsc] with r hA hAn hV hVn
  have hVr : Tendsto (fun n => f (φ (ψ n)) r) atTop
      (𝓝 (spectralHarmonicValue ell R u r)) := by
    simpa only [hVn,Function.comp_def] using hV.comp hψ.tendsto_atTop
  have hAr : Tendsto (fun n => (Real.sqrt ((ell : ℝ)*(ell+10)) : ℂ)*f (φ (ψ n)) r)
      atTop (𝓝 (spectralHarmonicAngularValue ell R u r)) := by
    simpa only [hAn] using hA
  exact tendsto_nhds_unique hAr (tendsto_const_nhds.mul hVr)

theorem spectralHarmonicCore_angular_zero (ell : ℕ) (R l : ℝ)
    (u : SpectralHarmonicEnergy ell R)
    (hu : (fun r => spectralHarmonicValue ell R u r) =ᵐ[(radialPressureMeasure R).restrict (Iic l)] 0) :
    (fun r => spectralHarmonicAngularValue ell R u r) =ᵐ[(spectralAngularMeasure R).restrict (Iic l)] 0 := by
  have hv : ∀ᵐ r ∂radialPressureMeasure R, r ≤ l → spectralHarmonicValue ell R u r=0 := by
    simpa only [mem_Iic,Pi.zero_apply] using (ae_restrict_iff' measurableSet_Iic).mp hu
  change ∀ᵐ r ∂(spectralAngularMeasure R).restrict (Iic l), spectralHarmonicAngularValue ell R u r=0
  rw [ae_restrict_iff' measurableSet_Iic]
  filter_upwards [spectralHarmonicAngularValue_ae ell R u,
    (spectralAngularMeasure_absolutelyContinuous R).ae_le hv] with r ha hv hr
  simp only [ha,hv hr,mul_zero]

end DefocusingNLS

end OAI
