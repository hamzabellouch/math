import OAI.Analysis.CircleDomains.Sobolev.PhysicalCircleSmoothing
import OAI.Analysis.CircleDomains.Selection.LogarithmicRectangleCover

namespace OAI

/-! Smoothing the actual physical mean on an open disk chart, with all
local logarithmic charts and the partition constructed internally. -/

open Set Function Filter MeasureTheory
open scoped Topology ENNReal NNReal

noncomputable section
namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩
variable [MeasurableSpace C(PathTime, Sphere)] [BorelSpace C(PathTime, Sphere)]

 theorem open_physical_mean_circle_smoothing
    (hsch : PlanarSchoenflies) (hsep : UnitDiskCrosscutSeparation)
    (hcoarea : PlanarLipschitzFiberCoarea)
    {G U : Set Sphere} (e : G ≃ₜ U) (hU : IsOpen U) (y₀ : Sphere)
    (π : Sphere → Sphere) (hπ : Continuous π) (he : ∀ y : G, (e y).val = π y.val)
    (A : Set C(PathTime, Sphere)) (hA : ∀ γ ∈ A, Injective γ)
    (η : ProbabilityMeasure A) (hfinite : ∀ γ ∈ A, physicalDomainLength e y₀ γ < ∞)
    (g : Sphere → ℝ≥0∞) (hg : Measurable g)
    (hocc : meanPhysicalOccupation e y₀ (η.map Subtype.val) = sphericalArea.withDensity g)
    (henergy : (∫⁻ p, g p ^ 2 ∂sphericalArea) < ∞)
    (K : Set C(PathTime, ℂ)) (hK : IsCompact K) (hKS : K ⊆ diskTerminalArcSet)
    (F : C(Sphere, ℂ)) (f : A → K) (hf : Measurable f)
    (hmap : ∀ γ : A, (f γ).val = F.comp γ.val)
    (D : TopologicalSpace.Opens ℂ) (hDG : MapsTo ((↑) : ℂ → Sphere) D G)
    (B : ℝ≥0) (hB : LipschitzOnWith B finiteCoord (((↑) : ℂ → Sphere) '' D))
    (hw0 : ∀ z ∈ D, F (π (z : Sphere)) ≠ 0)
    (hw1 : ∀ z ∈ D, ‖F (π (z : Sphere))‖ ≤ 1)
    (hF : ∀ γ : A, InjOn F (range γ.val ∪ (fun z : ℂ => π (z : Sphere)) '' D))
    (hinj : InjOn (fun z : ℂ => F (π (z : Sphere))) D)
    (hmiss : ∀ z ∈ D, ∀ᵐ γ : A ∂(η : Measure A), π (z : Sphere) ∉ range γ.val)
    (τ : EuclideanPlane → ℝ)
    (hτ : ContinuousOn τ (complexPlaneCoordinates ⁻¹' D))
    (hτpos : ∀ x ∈ complexPlaneCoordinates ⁻¹' D, 0 < τ x)
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    let Ω : TopologicalSpace.Opens EuclideanPlane :=
      ⟨complexPlaneCoordinates ⁻¹' D, D.isOpen.preimage complexPlaneCoordinates.continuous⟩
    let m : EuclideanPlane → UnitAddCircle := fun p =>
      diskMeanCircle hsch K hKS (η.map f) (F (π (planeSphere p)))
    ∃ (w : EuclideanPlane → UnitAddCircle) (R : EuclideanPlane → ℝ),
      FiniteTransfer.SmoothCircleOn w Ω ∧ ContinuousOn R Ω ∧
      (∀ x, w x = m x + (R x : UnitAddCircle)) ∧ (∀ x ∈ Ω, |R x| ≤ τ x) ∧
      ∀ i : Fin 2,
        MemLp (fun x => FiniteTransfer.circleFDeriv w x (EuclideanSpace.single i 1))
          2 (volume.restrict Ω) ∧
        eLpNorm (fun x => FiniteTransfer.circleFDeriv w x (EuclideanSpace.single i 1))
          2 (volume.restrict Ω) ≤ ε +
          eLpNorm (fun x : EuclideanPlane => (sliceChartDensity B g ⟨x 0, x 1⟩).toReal)
            2 (volume.restrict Ω) := by
  let Q : ℂ → ℂ := fun z => F (π (z : Sphere))
  have hQ : Continuous Q := F.continuous.comp (hπ.comp OnePoint.continuous_coe)
  obtain ⟨ι, hι, ρ, a₀, a, b, b₀, c₀, c, d, d₀, Ψ,
    hnest, hrect, hΨ, hpos, hproj, hsub⟩ :=
    exists_logarithmic_rectangle_partition D Q hQ.continuousOn hw0 hw1
  let : Countable ι := hι
  exact physical_mean_circle_smoothing hsch hsep hcoarea e hU y₀ π hπ he
    A hA η hfinite g hg hocc henergy K hK hKS F f hf hmap
    ρ a₀ a b b₀ c₀ c d d₀
    (fun j => (hnest j).1) (fun j => (hnest j).2.1) (fun j => (hnest j).2.2.1)
    (fun j => (hnest j).2.2.2.1) (fun j => (hnest j).2.2.2.2.1)
    (fun j => (hnest j).2.2.2.2.2)
    (fun j => hDG.mono_left (hrect j)) B
    (fun j => hB.mono (image_mono (hrect j))) Ψ hΨ hpos hproj
    (fun j γ => (hF γ).mono (union_subset_union Subset.rfl (image_mono (hrect j))))
    (fun j => hinj.mono (hrect j)) (fun j z hz => hmiss z (hrect j hz))
    hsub τ hτ hτpos hε

end CircleDomainRigidity

end

end OAI
