import OAI.Analysis.CircleDomains.Sobolev.OpenMeanCircleSmoothing
import OAI.Analysis.CircleDomains.Topology.LocalPlaneCorrection

namespace OAI

/-! Construct the single-valued quotient correction from the actual
physical smoothing. The tolerance and all dust limits are derived here. -/

open Set Function Filter MeasureTheory
open scoped Topology ENNReal NNReal

noncomputable section
namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩
variable [MeasurableSpace C(PathTime, Sphere)] [BorelSpace C(PathTime, Sphere)]

theorem exists_open_mean_circle_correction
    (hsch : PlanarSchoenflies) (hsep : UnitDiskCrosscutSeparation)
    (hcoarea : PlanarLipschitzFiberCoarea)
    {G U S : Set Sphere} (e : G ≃ₜ U) (hG : IsOpen G) (hU : IsOpen U) (hS : IsOpen S)
    (y₀ : Sphere) (π : Sphere → Sphere) (hπ : Continuous π)
    (he : ∀ y : G, (e y).val = π y.val) (hinf : π OnePoint.infty ∉ S)
    (hne : Uᶜ.Nonempty)
    (A : Set C(PathTime, Sphere)) (hA : ∀ γ ∈ A, Injective γ)
    (η : ProbabilityMeasure A) (hfinite : ∀ γ ∈ A, physicalDomainLength e y₀ γ < ∞)
    (g : Sphere → ℝ≥0∞) (hg : Measurable g)
    (hocc : meanPhysicalOccupation e y₀ (η.map Subtype.val) = sphericalArea.withDensity g)
    (henergy : (∫⁻ p, g p ^ 2 ∂sphericalArea) < ∞)
    (K : Set C(PathTime, ℂ)) (hK : IsCompact K) (hKS : K ⊆ diskTerminalArcSet)
    (F : C(Sphere, ℂ)) (f : A → K) (hf : Measurable f)
    (hmap : ∀ γ : A, (f γ).val = F.comp γ.val)
    (B : ℝ≥0) (hB : LipschitzOnWith B finiteCoord
      (((↑) : ℂ → Sphere) '' (((↑) : ℂ → Sphere) ⁻¹' G ∩
        (fun z : ℂ => π (z : Sphere)) ⁻¹' S)))
    (h0 : ∀ x ∈ S, F x ≠ 0) (h1 : ∀ x ∈ S, ‖F x‖ ≤ 1)
    (hF : ∀ γ : A, InjOn F (range γ.val ∪ S)) (hinj : InjOn F S)
    (hmiss : ∀ x ∈ U ∩ S, ∀ᵐ γ : A ∂(η : Measure A), x ∉ range γ.val)
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) {ε : ℝ≥0∞} (hε : 0 < ε) :
    let Ω : TopologicalSpace.Opens EuclideanPlane :=
      ⟨planeSphere ⁻¹' (G ∩ π ⁻¹' S), (hG.inter (hS.preimage hπ)).preimage continuous_planeSphere⟩
    ∃ (w : EuclideanPlane → UnitAddCircle) (R : Sphere → ℝ),
      FiniteTransfer.SmoothCircleOn w Ω ∧ ContinuousOn R (U ∩ S) ∧
      (∀ x, |R x| ≤ dustSmoothingTolerance id Uᶜ δ x) ∧
      (∀ x, |R x| ≤ 1) ∧
      (∀ x ∈ Uᶜ, Tendsto R (𝓝 x) (𝓝 0)) ∧
      (∀ p ∈ Ω, w p = diskMeanCircle hsch K hKS (η.map f)
        (F (π (planeSphere p))) + (R (π (planeSphere p)) : UnitAddCircle)) ∧
      ∀ i : Fin 2,
        MemLp (fun x => FiniteTransfer.circleFDeriv w x (EuclideanSpace.single i 1))
          2 (volume.restrict Ω) ∧
        eLpNorm (fun x => FiniteTransfer.circleFDeriv w x (EuclideanSpace.single i 1))
          2 (volume.restrict Ω) ≤ ε +
          eLpNorm (fun x : EuclideanPlane => (sliceChartDensity B g ⟨x 0, x 1⟩).toReal)
            2 (volume.restrict Ω) := by
  let D : TopologicalSpace.Opens ℂ :=
    ⟨((↑) : ℂ → Sphere) ⁻¹' G ∩ (fun z : ℂ => π (z : Sphere)) ⁻¹' S,
      (hG.preimage OnePoint.continuous_coe).inter
        (hS.preimage (hπ.comp OnePoint.continuous_coe))⟩
  have hqU (z : ℂ) (hz : z ∈ D) : π (z : Sphere) ∈ U := by
    rw [← he ⟨(z : Sphere), hz.1⟩]
    exact (e ⟨(z : Sphere), hz.1⟩).property
  have hQinj : InjOn (fun z : ℂ => F (π (z : Sphere))) D := by
    intro z hz t ht heq
    have hqt := hinj hz.2 ht.2 heq
    have het : e ⟨(z : Sphere), hz.1⟩ = e ⟨(t : Sphere), ht.1⟩ :=
      Subtype.ext ((he ⟨(z : Sphere), hz.1⟩).trans
        (hqt.trans (he ⟨(t : Sphere), ht.1⟩).symm))
    exact OnePoint.coe_injective (congrArg Subtype.val (e.injective het))
  let τ := dustSmoothingTolerance (π ∘ planeSphere) Uᶜ δ
  have hτ : Continuous τ := continuous_dustSmoothingTolerance
    (hπ.comp continuous_planeSphere) Uᶜ δ
  have hτpos : ∀ p ∈ complexPlaneCoordinates ⁻¹' D, 0 < τ p := by
    intro p hp
    apply dustSmoothingTolerance_pos (π ∘ planeSphere) hU.isClosed_compl hne hδ
    exact fun hn => hn (hqU (complexPlaneCoordinates p) hp)
  obtain ⟨w, r, hw, hr, hwr, hrtol, hgrad⟩ := open_physical_mean_circle_smoothing
    hsch hsep hcoarea e hU y₀ π hπ he A hA η hfinite g hg hocc henergy
    K hK hKS F f hf hmap D (fun _ hz => hz.1) B hB
    (fun z hz => h0 _ hz.2) (fun z hz => h1 _ hz.2)
    (fun γ => (hF γ).mono (union_subset_union Subset.rfl (by
      rintro _ ⟨z, hz, rfl⟩
      exact hz.2))) hQinj (fun z hz => hmiss _ ⟨hqU z hz, hz.2⟩)
    τ hτ.continuousOn hτpos hε
  change ContinuousOn r (planeSphere ⁻¹' (G ∩ π ⁻¹' S)) at hr
  change ∀ p ∈ planeSphere ⁻¹' (G ∩ π ⁻¹' S),
    |r p| ≤ dustSmoothingTolerance (π ∘ planeSphere) Uᶜ δ p at hrtol
  obtain ⟨R, hRc, hRp, hRb, hR1, hRlim⟩ := exists_local_plane_correction e hG hS π hπ he
    hinf δ ⟨hδ.le, hδ1⟩ r hr hrtol
  refine ⟨w, R, hw, hRc, hRb, hR1, hRlim, ?_, hgrad⟩
  intro p hp
  rw [hRp p hp]
  exact hwr p

end CircleDomainRigidity

end

end OAI
