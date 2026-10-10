import OAI.Analysis.CircleDomains.Sobolev.PhysicalMeanIndexSobolev
import OAI.Analysis.CircleDomains.Sobolev.WeightedSobolevTransport

namespace OAI

/-! The actual local mean-index weak derivatives, transported to the
Euclidean Sobolev witness used by positive partition smoothing. -/

open Set Function Filter MeasureTheory
open scoped Topology ENNReal NNReal

noncomputable section
namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩
variable [MeasurableSpace C(PathTime, Sphere)] [BorelSpace C(PathTime, Sphere)]

 theorem physicalMeanIndex_rectangle_sobolev_witness
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
    {a₀ a b b₀ c₀ c d d₀ : ℝ}
    (ha : a₀ < a) (hab : a < b) (hb : b < b₀)
    (hc : c₀ < c) (hcd : c < d) (hd : d < d₀)
    (hAG : MapsTo ((↑) : ℂ → Sphere) (planarSliceBox (Icc a₀ b₀) (Icc c₀ d₀)) G)
    (B : ℝ≥0) (hB : LipschitzOnWith B finiteCoord
      (((↑) : ℂ → Sphere) '' planarSliceBox (Icc a₀ b₀) (Icc c₀ d₀)))
    (Ψ : ℂ → ℂ) (hΨ : ContinuousOn Ψ (planarSliceBox (Icc a₀ b₀) (Icc c₀ d₀)))
    (hpos : ∀ z ∈ planarSliceBox (Icc a₀ b₀) (Icc c₀ d₀), 0 ≤ (Ψ z).im)
    (hproj : ∀ z ∈ planarSliceBox (Icc a₀ b₀) (Icc c₀ d₀),
      diskRayProjection (Ψ z) = F (π (z : Sphere)))
    (hF : ∀ γ : A, InjOn F (range γ.val ∪
      (fun z : ℂ => π (z : Sphere)) '' planarSliceBox (Icc a₀ b₀) (Icc c₀ d₀)))
    (hinj : InjOn (fun z : ℂ => F (π (z : Sphere)))
      (planarSliceBox (Icc a₀ b₀) (Icc c₀ d₀))) :
    let v := liftedMeanGeometricIndex hsch K hKS (η.map f) Ψ
    let v₂ : EuclideanPlane → ℝ := fun p => v ⟨p 0, p 1⟩
    ∃ H : DeGiorgi.MemW1pWitness 2 v₂
      (euclideanPlaneCoordinates ⁻¹' (Ioo a b ×ˢ Ioo c d)),
      ∀ i : Fin 2, ∀ᵐ p ∂volume.restrict
        (euclideanPlaneCoordinates ⁻¹' (Ioo a b ×ˢ Ioo c d)),
        |H.weakGrad p i| ≤ (sliceChartDensity B g ⟨p 0, p 1⟩).toReal := by
  obtain ⟨hm, Gx, Gy, _, _, hx, hy, hbound, hweak⟩ :=
    physicalMeanIndex_rectangle_weak_gradient hsch hsep hcoarea e hU y₀ π hπ he
      A hA η hfinite g hg hocc henergy K hK hKS F f hf hmap
      ha hab hb hc hcd hd hAG B hB Ψ hΨ hpos hproj hF hinj
  exact exists_bounded_rectangle_sobolev_witness hm hx hy hbound hweak

end CircleDomainRigidity

end

end OAI
