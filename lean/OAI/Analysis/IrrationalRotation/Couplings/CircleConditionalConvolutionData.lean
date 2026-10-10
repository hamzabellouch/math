import OAI.Analysis.IrrationalRotation.Rotation.CircleTruncationIntegral
import OAI.Analysis.IrrationalRotation.Rotation.CircleTailExceptionalFamilies
import OAI.Analysis.IrrationalRotation.Rotation.CircleOrderedTransfer
import OAI.Analysis.IrrationalRotation.Analysis.ParameterConvolutionIdentity
import OAI.Analysis.IrrationalRotation.Rotation.CircleObstruction

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped lp ComplexConjugate
namespace Invariant233.CircleCoupling
open InvariantProjection.ConditionalConvolution
variable {θ : ℝ} {p : CircleParameterData} (hp : CircleParameterLaws θ p)
include hp

theorem conditionalData_of_truncation_mass
    (j : ℕ) (hj : 1 ≤ j) (hr : ∀ i, 0 < MixedRadix.radices p.q i)
    {P : Rotation.Hilbert →L[ℂ] Rotation.Hilbert}
    (hmem : P ∈ Rotation.algebra θ) (hP : IsStarProjection P)
    (hT : (1 - P) * p.measurableOperator θ hp * P = 0)
    (F : Circle → Rotation.Fiber →L[ℂ] Rotation.Fiber)
    (hF : ∀ z, IsStarProjection (F z))
    (hFm : ∀ v : Rotation.Fiber, StronglyMeasurable (fun z => F z v))
    (hrep : ∀ ξ : Rotation.Hilbert, P ξ =ᵐ[circleMeasure] fun z => F z (ξ z))
    (c : ℝ) (hmass : c ≤ (law p j).real (truncationEvent p j hr
      (fun z => ((F z ProjectionCocycleWindow.basisZero) 0).re))) :
    Nonempty (Data Sample (law p j) (p.K j) (p.coefficientBound j)
      (1 / (j : ℝ)) c (Real.exp (-p.L j)) (Real.exp (-p.L j / 400))) := by
  classical
  let := law_isProbabilityMeasure hp j
  let r : Circle → ℝ := fun z => ((F z ProjectionCocycleWindow.basisZero) 0).re
  let E := truncationEvent p j hr r
  let ξ : Sample → Rotation.Fiber := fun ω =>
    F (point p hr false ω) ProjectionCocycleWindow.basisZero
  let γ : Sample → Rotation.Fiber := fun ω =>
    (1 - F (point p hr true ω)) ProjectionCocycleWindow.basisZero
  let Fx : Sample → ℤ → ℝ := fun ω k => p.floorCocycle θ k (point p hr false ω)
  let Fy : Sample → ℤ → ℝ := fun ω k => p.floorCocycle θ k (point p hr true ω)
  have hrm : Measurable r := Complex.continuous_re.measurable.comp
    (((lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 0).continuous.comp_stronglyMeasurable
      (hFm ProjectionCocycleWindow.basisZero)).measurable)
  have hEm : MeasurableSet E := measurableSet_truncationEvent hp j hr hrm
  obtain ⟨H₁, H₂, hm₁, hm₂, hc₁, hc₂, hatt⟩ :=
    tail_exceptional_families_of_subset hp j hj hr E hEm
      (truncationEvent_subset_tagEvent p j hr r)
  have hordered := orderedCouplingIdentities_of_rational hp hr F hF
    (fun k => (hFm (lp.single 2 k 1)).measurable)
    (hp.rational_graphs_of_representation hmem hP hT F hrep) j
  have hbound := hordered.mono (fun _ h k => (h.2 k).2)
  have hzero := hp.ae_parameter_convolution_absolute_and_zero (law p j)
    (point p hr false) (point p hr true) (measurable_point hp hr true).aemeasurable
    (endpoint_absolutelyContinuous hp j hr true) F hF hrep hT
    (hordered.mono (fun _ h => h.1)) hbound
  have hratio := hp.ae_parameter_convolution_ratio_bounds (law p j)
    (point p hr false) (point p hr true) (measurable_point hp hr false).aemeasurable
    (measurable_point hp hr true).aemeasurable
    (endpoint_absolutelyContinuous hp j hr false)
    (endpoint_absolutelyContinuous hp j hr true) hbound
  have hγm : StronglyMeasurable (fun z =>
      (1 - F z) ProjectionCocycleWindow.basisZero) := by
    have h : StronglyMeasurable
        ((fun _ : Circle => ProjectionCocycleWindow.basisZero) -
          fun z => F z ProjectionCocycleWindow.basisZero) :=
      stronglyMeasurable_const.sub (hFm ProjectionCocycleWindow.basisZero)
    convert h using 1
    funext z
    simp only [Pi.sub_apply, sub_apply, one_apply_eq_self]
  refine ⟨{
    mX := endpointSigma p hr false
    mY := endpointSigma p hr true
    mX_le := (measurable_point hp hr false).comap_le
    mY_le := (measurable_point hp hr true).comap_le
    ξ := ξ
    γ := γ
    ξ_measurable := (hFm ProjectionCocycleWindow.basisZero).comp_measurable
      (measurable_iff_comap_le.mpr le_rfl)
    γ_measurable := hγm.comp_measurable (measurable_iff_comap_le.mpr le_rfl)
    ξ_unit := Eventually.of_forall (fun ω =>
      ProjectionCocycleWindow.projection_vector_norm_le _ (hF _))
    γ_unit := Eventually.of_forall (fun ω =>
      ProjectionCocycleWindow.complement_vector_norm_le _ (hF _))
    Fx := Fx
    Fy := Fy
    Fx_measurable := fun k => (hp.measurable_parameter_cocycle k).comp
      (measurable_point hp hr false)
    Fy_measurable := fun k => (hp.measurable_parameter_cocycle k).comp
      (measurable_point hp hr true)
    Fx_pos := Eventually.of_forall (fun ω k => p.floorCocycle_pos θ k _)
    Fy_pos := Eventually.of_forall (fun ω k => p.floorCocycle_pos θ k _)
    Fx_zero := Eventually.of_forall (fun ω => p.floorCocycle_zero θ _)
    Fy_zero := Eventually.of_forall (fun ω => p.floorCocycle_zero θ _)
    zero_convolution := ?_
    ratio_bounds := fun n _ => hratio.mono (fun _ h => h n)
    E := E
    E_measurable := hEm
    E_mass := hmass
    coefficient_bounds := ?_
    H₁ := H₁
    H₂ := H₂
    H₁_measurable := hm₁
    H₂_measurable := hm₂
    attenuation := hatt
    conditional₁ := hc₁
    conditional₂ := hc₂ }⟩
  · intro n _
    filter_upwards [hzero] with ω hω
    exact (hω n ProjectionCocycleWindow.basisZero ProjectionCocycleWindow.basisZero).2
  · filter_upwards [ae_restrict_mem hEm,
      ae_restrict_of_ae (ae_truncationEvent_exclusions hp j hj hr r)] with ω hω he
    have he' := he hω
    have hdiag := hω.2.2.2.2
    have hright : ((F (point p hr true ω) ProjectionCocycleWindow.basisZero) 0).re ≤
        1 - 1 / (j : ℝ) := by
      change 1 / (j : ℝ) ≤ 1 - ((F (point p hr true ω)
        ProjectionCocycleWindow.basisZero) 0).re at hdiag
      linarith
    exact hp.canonical_projection_coefficient_properties j hj _ _
      (fun s hs i hi => (he' s hs i hi).1) (fun s hs i hi => (he' s hs i hi).2)
      _ _ (hF _) (hF _) (1 / (j : ℝ)) hω.2.2.2.1 hright

end Invariant233.CircleCoupling

end

end OAI
