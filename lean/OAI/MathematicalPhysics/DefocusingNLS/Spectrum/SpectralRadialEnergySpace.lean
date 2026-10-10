import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralPressureOperator
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions

namespace OAI

/-! The completed radial H¹ energy space on the fixed twelve-dimensional ball.

The two ambient coordinates are the radial value and its weak derivative.
Taking the closure of smooth jets keeps their compatibility in the completion.
-/

open Set MeasureTheory
open scoped SchwartzMap
namespace DefocusingNLS

noncomputable abbrev SpectralRadialL2 (R : ℝ) := Lp ℂ 2 (radialPressureMeasure R)

noncomputable abbrev SpectralRadialJetSpace (R : ℝ) :=
  WithLp 2 (SpectralRadialL2 R × SpectralRadialL2 R)

noncomputable def spectralRadialSmoothValue (R : ℝ) :
    𝓢(ℝ,ℂ) →L[ℂ] SpectralRadialL2 R :=
  (BoundedContinuousFunction.toLp 2 (radialPressureMeasure R) ℂ).comp
    (SchwartzMap.toBoundedContinuousFunctionCLM ℂ ℝ ℂ)

noncomputable def spectralRadialSmoothJet (R : ℝ) :
    𝓢(ℝ,ℂ) →L[ℂ] SpectralRadialJetSpace R :=
  (WithLp.prodContinuousLinearEquiv 2 ℂ (SpectralRadialL2 R) (SpectralRadialL2 R)).symm.toContinuousLinearMap.comp
      ((spectralRadialSmoothValue R).prod
        ((spectralRadialSmoothValue R).comp (SchwartzMap.derivCLM ℂ ℂ)))

noncomputable def spectralRadialEnergySubspace (R : ℝ) :
    Submodule ℂ (SpectralRadialJetSpace R) :=
  (LinearMap.range (spectralRadialSmoothJet R).toLinearMap).topologicalClosure

noncomputable abbrev SpectralRadialEnergy (R : ℝ) := spectralRadialEnergySubspace R

instance spectralRadialEnergy_complete (R : ℝ) : CompleteSpace (SpectralRadialEnergy R) :=
  Submodule.topologicalClosure.completeSpace _

noncomputable def spectralRadialValue (R : ℝ) :
    SpectralRadialEnergy R →L[ℂ] SpectralRadialL2 R :=
  (WithLp.fstL 2 ℂ (SpectralRadialL2 R) (SpectralRadialL2 R)).comp
    (spectralRadialEnergySubspace R).subtypeL

noncomputable def spectralRadialDerivative (R : ℝ) :
    SpectralRadialEnergy R →L[ℂ] SpectralRadialL2 R :=
  (WithLp.sndL 2 ℂ (SpectralRadialL2 R) (SpectralRadialL2 R)).comp
    (spectralRadialEnergySubspace R).subtypeL

theorem spectralRadialEnergy_norm_sq (R : ℝ) (u : SpectralRadialEnergy R) :
    ‖u‖^2=‖spectralRadialValue R u‖^2+‖spectralRadialDerivative R u‖^2 := by
  change ‖(u : SpectralRadialJetSpace R)‖^2=
    ‖(u : SpectralRadialJetSpace R).fst‖^2+‖(u : SpectralRadialJetSpace R).snd‖^2
  exact WithLp.prod_norm_sq_eq_of_L2 _

noncomputable def spectralRadialSmoothEmbedding (R : ℝ) :
    𝓢(ℝ,ℂ) →L[ℂ] SpectralRadialEnergy R :=
  (spectralRadialSmoothJet R).codRestrict (spectralRadialEnergySubspace R) (fun f =>
    (LinearMap.range (spectralRadialSmoothJet R).toLinearMap).le_topologicalClosure ⟨f,rfl⟩)

theorem spectralRadialSmoothEmbedding_dense (R : ℝ) :
    DenseRange (spectralRadialSmoothEmbedding R) := by
  let j := spectralRadialSmoothJet R
  let ff : 𝓢(ℝ,ℂ) → closure (range j) := inclusion subset_closure ∘ rangeFactorization j
  have h : DenseRange ff :=
    ((denseRange_inclusion_iff subset_closure).2 subset_rfl).comp
      rangeFactorization_surjective.denseRange (continuous_inclusion subset_closure)
  exact h

theorem spectralRadialSmoothEmbedding_value (R : ℝ) (f : 𝓢(ℝ,ℂ)) :
    spectralRadialValue R (spectralRadialSmoothEmbedding R f)=spectralRadialSmoothValue R f := rfl

theorem spectralRadialSmoothEmbedding_derivative (R : ℝ) (f : 𝓢(ℝ,ℂ)) :
    spectralRadialDerivative R (spectralRadialSmoothEmbedding R f)=
      spectralRadialSmoothValue R (SchwartzMap.derivCLM ℂ ℂ f) := rfl

end DefocusingNLS

end OAI
