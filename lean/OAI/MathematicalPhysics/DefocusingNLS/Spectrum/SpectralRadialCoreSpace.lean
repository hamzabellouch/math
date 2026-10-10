import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralRadialTraceEvaluation
import Mathlib.Analysis.Normed.Operator.Compact.Basic

namespace OAI

/-! The fixed-harmonic energy pair and its closed constrained core domain. -/

open Set MeasureTheory
namespace DefocusingNLS

noncomputable instance spectralRadialEnergy_realInner (R : ℝ) :
    InnerProductSpace ℝ (SpectralRadialEnergy R) :=
  InnerProductSpace.complexToReal

noncomputable abbrev SpectralRadialPairEnergy (R : ℝ) :=
  WithLp 2 (SpectralRadialEnergy R × SpectralRadialEnergy R)

noncomputable def spectralRadialFirstValue (R : ℝ) :
    SpectralRadialPairEnergy R →L[ℝ] SpectralRadialL2 R :=
  ((spectralRadialValue R).comp
    (WithLp.fstL 2 ℂ (SpectralRadialEnergy R) (SpectralRadialEnergy R))).restrictScalars ℝ

noncomputable def spectralRadialPairTrace (R : ℝ) (hR : 0 < R) :
    SpectralRadialPairEnergy R →L[ℂ] ℂ × ℂ :=
  ((spectralRadialTrace R hR).comp
    (WithLp.fstL 2 ℂ (SpectralRadialEnergy R) (SpectralRadialEnergy R))).prod
  ((spectralRadialTrace R hR).comp
    (WithLp.sndL 2 ℂ (SpectralRadialEnergy R) (SpectralRadialEnergy R)))

theorem spectralRadialPairTrace_compact (R : ℝ) (hR : 0 < R) :
    IsCompactOperator (spectralRadialPairTrace R hR) :=
  isCompactOperator_of_locallyCompactSpace_dom _

private theorem coreIndicator_measurable (l : ℝ) :
    Measurable ((Iic l).indicator (fun _ : ℝ => (1 : ℝ))) :=
  measurable_const.indicator measurableSet_Iic

private theorem coreIndicator_bound (R l : ℝ) :
    ∀ᵐ r ∂radialPressureMeasure R, ‖(Iic l).indicator (fun _ : ℝ => (1 : ℝ)) r‖ ≤ 1 := by
  apply Filter.Eventually.of_forall
  intro r
  by_cases hr : r ∈ Iic l <;> simp [hr]

noncomputable def spectralRadialCoreMask (R l : ℝ) :
    SpectralRadialL2 R →L[ℝ] SpectralRadialL2 R :=
  spectralPressureOperator R ((Iic l).indicator (fun _ : ℝ => (1 : ℝ)))
    (coreIndicator_measurable l).aestronglyMeasurable (coreIndicator_bound R l)

theorem spectralRadialCoreMask_zero (R l : ℝ) (u : SpectralRadialL2 R) :
    spectralRadialCoreMask R l u=0 ↔
      (fun r => u r) =ᵐ[(radialPressureMeasure R).restrict (Iic l)] 0 := by
  have hm := spectralPressureProduct_ae R ((Iic l).indicator (fun _ : ℝ => (1 : ℝ)))
    (coreIndicator_measurable l).aestronglyMeasurable (coreIndicator_bound R l) u
  change (fun r => spectralRadialCoreMask R l u r) =ᵐ[radialPressureMeasure R]
    (fun r => (Iic l).indicator (fun _ : ℝ => (1 : ℝ)) r • u r) at hm
  change spectralRadialCoreMask R l u=0 ↔
    ∀ᵐ r ∂(radialPressureMeasure R).restrict (Iic l), u r=0
  rw [ae_restrict_iff' measurableSet_Iic]
  constructor
  · intro hz
    have hz' := (Lp.ext_iff.mp hz).trans (Lp.coeFn_zero ℂ 2 (radialPressureMeasure R))
    filter_upwards [hm,hz'] with r hr hz hrmem
    simpa only [indicator_of_mem hrmem,one_smul,Pi.zero_apply] using hr.symm.trans hz
  · intro hz
    apply Lp.ext
    filter_upwards [hm,hz,Lp.coeFn_zero ℂ 2 (radialPressureMeasure R)] with r hr hz hzero
    rw [hr,hzero]
    by_cases hrmem : r ∈ Iic l
    · simp only [indicator_of_mem hrmem,one_smul,hz hrmem,Pi.zero_apply]
    · simp only [indicator_of_notMem hrmem,zero_smul,Pi.zero_apply]

noncomputable def spectralRadialCoreSubspace (R l : ℝ) :
    Submodule ℝ (SpectralRadialPairEnergy R) :=
  ((spectralRadialCoreMask R l).comp (spectralRadialFirstValue R)).ker

noncomputable abbrev SpectralRadialCoreEnergy (R l : ℝ) := spectralRadialCoreSubspace R l

instance spectralRadialCoreEnergy_complete (R l : ℝ) :
    CompleteSpace (SpectralRadialCoreEnergy R l) := by
  change CompleteSpace (((spectralRadialCoreMask R l).comp (spectralRadialFirstValue R)).ker)
  infer_instance

theorem spectralRadialCoreSubspace_mem (R l : ℝ) (u : SpectralRadialPairEnergy R) :
    u ∈ spectralRadialCoreSubspace R l ↔
      (fun r => spectralRadialFirstValue R u r) =ᵐ[(radialPressureMeasure R).restrict (Iic l)] 0 :=
  spectralRadialCoreMask_zero R l (spectralRadialFirstValue R u)

end DefocusingNLS

end OAI
