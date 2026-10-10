import OAI.Analysis.CircleDomains.Selection.ContinuousMeanIndexWitness
import OAI.Analysis.CircleDomains.Sobolev.SliceDensityLp
import OAI.Analysis.CircleDomains.Sobolev.CircleSmoothingBands

namespace OAI

/-! Positive smoothing of the actual circle-valued mean of the physical
arc law. Every local Sobolev witness is derived from occupation and coarea;
the smoothing discrepancy obeys the prescribed pointwise tolerance. -/

open Set Function Filter MeasureTheory
open scoped Topology ENNReal NNReal

noncomputable section
namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩


variable [MeasurableSpace C(PathTime, Sphere)] [BorelSpace C(PathTime, Sphere)]

 theorem physical_mean_circle_smoothing
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
    {Ω : TopologicalSpace.Opens EuclideanPlane} {ι : Type*} [Countable ι]
    (ρ : OpenPlanePartition Ω ι) (a₀ a b b₀ c₀ c d d₀ : ι → ℝ)
    (ha : ∀ j, a₀ j < a j) (hab : ∀ j, a j < b j) (hb : ∀ j, b j < b₀ j)
    (hc : ∀ j, c₀ j < c j) (hcd : ∀ j, c j < d j) (hd : ∀ j, d j < d₀ j)
    (hAG : ∀ j, MapsTo ((↑) : ℂ → Sphere)
      (planarSliceBox (Icc (a₀ j) (b₀ j)) (Icc (c₀ j) (d₀ j))) G)
    (B : ℝ≥0) (hB : ∀ j, LipschitzOnWith B finiteCoord
      (((↑) : ℂ → Sphere) '' planarSliceBox (Icc (a₀ j) (b₀ j)) (Icc (c₀ j) (d₀ j))))
    (Ψ : ι → ℂ → ℂ) (hΨ : ∀ j, ContinuousOn (Ψ j)
      (planarSliceBox (Icc (a₀ j) (b₀ j)) (Icc (c₀ j) (d₀ j))))
    (hpos : ∀ j z, z ∈ planarSliceBox (Icc (a₀ j) (b₀ j)) (Icc (c₀ j) (d₀ j)) →
      0 ≤ (Ψ j z).im)
    (hproj : ∀ j z, z ∈ planarSliceBox (Icc (a₀ j) (b₀ j)) (Icc (c₀ j) (d₀ j)) →
      diskRayProjection (Ψ j z) = F (π (z : Sphere)))
    (hF : ∀ j (γ : A), InjOn F (range γ.val ∪
      (fun z : ℂ => π (z : Sphere)) '' planarSliceBox (Icc (a₀ j) (b₀ j)) (Icc (c₀ j) (d₀ j))))
    (hinj : ∀ j, InjOn (fun z : ℂ => F (π (z : Sphere)))
      (planarSliceBox (Icc (a₀ j) (b₀ j)) (Icc (c₀ j) (d₀ j))))
    (hmiss : ∀ j z, z ∈ planarSliceBox (Icc (a₀ j) (b₀ j)) (Icc (c₀ j) (d₀ j)) →
      ∀ᵐ γ : A ∂(η : Measure A), π (z : Sphere) ∉ range γ.val)
    (hsub : ∀ j, tsupport (ρ.weight j) ⊆
      euclideanPlaneCoordinates ⁻¹' (Ioo (a j) (b j) ×ˢ Ioo (c j) (d j)))
    (τ : EuclideanPlane → ℝ) (hτ : ContinuousOn τ Ω) (hτpos : ∀ x ∈ Ω, 0 < τ x)
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    let m : EuclideanPlane → UnitAddCircle := fun p =>
      diskMeanCircle hsch K hKS (η.map f) (F (π ((⟨p 0, p 1⟩ : ℂ) : Sphere)))
    ∃ (w : EuclideanPlane → UnitAddCircle) (R : EuclideanPlane → ℝ),
      FiniteTransfer.SmoothCircleOn w Ω ∧ ContinuousOn R Ω ∧ (∀ x, w x = m x + (R x : UnitAddCircle)) ∧
      (∀ x ∈ Ω, |R x| ≤ τ x) ∧
      ∀ i : Fin 2,
        MemLp (fun x => FiniteTransfer.circleFDeriv w x (EuclideanSpace.single i 1))
          2 (volume.restrict Ω) ∧
        eLpNorm (fun x => FiniteTransfer.circleFDeriv w x (EuclideanSpace.single i 1))
          2 (volume.restrict Ω) ≤ ε +
          eLpNorm (fun x : EuclideanPlane => (sliceChartDensity B g ⟨x 0, x 1⟩).toReal)
            2 (volume.restrict Ω) := by
  let W : ι → Set EuclideanPlane := fun j =>
    euclideanPlaneCoordinates ⁻¹' (Ioo (a j) (b j) ×ˢ Ioo (c j) (d j))
  let u : ι → EuclideanPlane → ℝ := fun j p =>
    liftedMeanGeometricIndex hsch K hKS (η.map f) (Ψ j) ⟨p 0, p 1⟩
  let m : EuclideanPlane → UnitAddCircle := fun p =>
    diskMeanCircle hsch K hKS (η.map f) (F (π ((⟨p 0, p 1⟩ : ℂ) : Sphere)))
  have hW (j : ι) : IsOpen (W j) :=
    (isOpen_Ioo.prod isOpen_Ioo).preimage euclideanPlaneCoordinates.continuous
  have hlocal (j : ι) := continuous_meanIndex_rectangle_witness hsch hsep hcoarea e hU y₀ π hπ he
    A hA η hfinite g hg hocc henergy K hK hKS F f hf hmap
    (ha j) (hab j) (hb j) (hc j) (hcd j) (hd j) (hAG j) B (hB j) (Ψ j)
    (hΨ j) (hpos j) (hproj j) (hF j) (hinj j) (hmiss j)
  choose H hH using fun j => (hlocal j).2.2
  obtain ⟨v, hv, hs, hvalue, herr⟩ := exists_circle_smoothing_with_tolerance
    ρ W hW hsub m u (fun j => (hlocal j).1) (fun j => (hlocal j).2.1) H τ hτ hτpos hε
  refine ⟨ρ.circleMix m u v, ρ.mix (fun j x => v j x - u j x), hs,
    ρ.mix_sub_continuousOn W hW hsub u v (fun j => (hlocal j).1)
      (fun j => (hv j).1.1.continuous), (fun _ => rfl), hvalue, ?_⟩
  intro i
  exact partition_field_energy ρ W (fun j => (hW j).measurableSet) hsub
    (fun j x => (H j).weakGrad x i)
    (fun j => ((H j).weakGrad_component_memLp i).aestronglyMeasurable)
    ((sliceChartDensity_euclidean_memLp B g hg henergy).restrict Ω)
    (fun j => hH j i) (herr i)

end CircleDomainRigidity

end

end OAI
