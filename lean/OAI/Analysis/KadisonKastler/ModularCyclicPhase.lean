import OAI.Analysis.KadisonKastler.ResolventMeasureFaithful
import OAI.Analysis.KadisonKastler.ResolventMultiplierBounds
import OAI.Analysis.KadisonKastler.ResolventMultiplierLimit
import OAI.Analysis.KadisonKastler.ModularSpectralPhase

namespace OAI

/-! # The modular group in the cyclic spectral model

The two injective graph coordinates exclude the endpoints. Dominated
convergence then identifies the strong-limit group with the logarithmic
phase multiplier on every scalar cyclic spectral space.
-/

namespace KadisonKastler

open MeasureTheory Filter
open scoped Topology

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

theorem graphResolventVectorMeasure_interior (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H)
    (hsep : Function.Injective (algebraVectorMap M Ω))
    (hcyc : DenseRange (algebraVectorMap M Ω)) (x : H) :
    ∀ᵐ s ∂resolventVectorMeasure (graphResolvent M J Ω 1)
      (graphResolvent_positive J Ω 1).isSelfAdjoint x, 0 < s.val ∧ s.val < 1 := by
  have h0 := measure_eq_zero_iff_ae_notMem.mp
    (resolventVectorMeasure_zero_endpoint (graphResolvent M J Ω 1)
      (graphResolvent_positive J Ω 1).isSelfAdjoint (graphResolvent_injective J Ω hsep hcyc) x)
  have h1 := measure_eq_zero_iff_ae_notMem.mp
    (resolventVectorMeasure_one_endpoint (graphResolvent M J Ω 1)
      (graphResolvent_positive J Ω 1).isSelfAdjoint (one_sub_graphResolvent_injective J Ω hsep) x)
  filter_upwards [h0, h1] with s h0 h1
  have hb := graphResolvent_spectrum_bounds J Ω s.property
  change s.val ≠ 0 at h0
  change s.val ≠ 1 at h1
  exact ⟨lt_of_le_of_ne hb.1 h0.symm, lt_of_le_of_ne hb.2 h1⟩

variable [TopologicalSpace.SeparableSpace H]

theorem modularStrongLimit_cyclic (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H)
    (hsep : Function.Injective (algebraVectorMap M Ω))
    (hcyc : DenseRange (algebraVectorMap M Ω)) (x : H) (t : ℝ)
    (v : ResolventCyclicL2 (graphResolvent M J Ω 1)
      (graphResolvent_positive J Ω 1).isSelfAdjoint x) :
    resolventCyclicIsometry _ (graphResolvent_positive J Ω 1).isSelfAdjoint x
      (resolventScalarMultiplier _ (graphResolvent_positive J Ω 1).isSelfAdjoint x
        (fun s => modularSpectralPhase t s.val)
        ((modularSpectralPhase_measurable t).comp measurable_subtype_coe)
        1 (fun s => (modularSpectralPhase_norm t s.val).le) v) =
      modularStrongLimit J Ω hsep hcyc t
        (resolventCyclicIsometry _ (graphResolvent_positive J Ω 1).isSelfAdjoint x v) := by
  let R := graphResolvent M J Ω 1
  have hR : IsSelfAdjoint R := (graphResolvent_positive J Ω 1).isSelfAdjoint
  let g : ℕ → C(spectrum ℝ R, ℂ) := fun n =>
    ⟨fun s => modularPhaseScalar t (modularRegularizationScale n) (s.val : ℂ),
      ((modularPhaseScalar_continuousOn J Ω t (modularRegularizationScale_pos n)).comp
        Complex.continuous_ofReal.continuousOn (fun _ hs => spectrum.algebraMap_mem ℂ hs)).domRestrict⟩
  have hb (n : ℕ) (s : spectrum ℝ R) : ‖g n s‖ ≤ 1 :=
    (modularPhaseScalar_norm _ _ _).le
  have hpt : ∀ᵐ s ∂resolventVectorMeasure R hR x,
      Tendsto (fun n => g n s) atTop (𝓝 (modularSpectralPhase t s.val)) := by
    filter_upwards [graphResolventVectorMeasure_interior J Ω hsep hcyc x] with s hs
    exact modularPhaseScalar_tendsto t hs.1 hs.2
  have ht := resolventScalarMultiplier_tendsto R hR x (fun n => g n)
    (fun s => modularSpectralPhase t s.val) (fun n => (g n).continuous.measurable)
    ((modularSpectralPhase_measurable t).comp measurable_subtype_coe) hb
    (fun s => (modularSpectralPhase_norm t s.val).le) hpt v
  have he (n : ℕ) : resolventContinuousCalculus R hR (g n) =
      modularApproximation M J Ω n t := by
    rw [modularApproximation, regularizedModularGroup_eq_cfc J Ω t
      (modularRegularizationScale_pos n)]
    have hc : ContinuousOn (fun s : ℝ =>
        modularPhaseScalar t (modularRegularizationScale n) (s : ℂ)) (spectrum ℝ R) :=
      (modularPhaseScalar_continuousOn J Ω t (modularRegularizationScale_pos n)).comp
        Complex.continuous_ofReal.continuousOn (fun _ hs => spectrum.algebraMap_mem ℂ hs)
    have hh := resolventContinuousCalculus_eq_cfc R hR _ hc
    calc
      _ = cfc (fun z : ℂ => modularPhaseScalar t (modularRegularizationScale n)
        (z.re : ℂ)) R := hh
      _ = _ := by
        apply cfc_congr
        intro z _
        simp only [modularPhaseScalar, Complex.ofReal_re]
  have hlim := (resolventCyclicIsometry R hR x).continuous.continuousAt.tendsto.comp ht
  apply tendsto_nhds_unique hlim
  apply (modularApproximation_tendsto J Ω hsep hcyc t
    (resolventCyclicIsometry R hR x v)).congr
  intro n
  dsimp only [Function.comp_def]
  rw [resolventCyclicIsometry_multiplier_of_bound, he]

end

end KadisonKastler

end OAI
