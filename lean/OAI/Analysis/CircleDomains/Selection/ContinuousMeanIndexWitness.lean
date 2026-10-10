import OAI.Analysis.CircleDomains.Selection.PhysicalMeanIndexWitness
import OAI.Analysis.CircleDomains.Topology.MeanIndexCircle

namespace OAI

/-! Continuous Sobolev branches of the actual descended mean circle map.
Continuity is derived from avoidance of each physical point by the source law. -/

open Set Function Filter MeasureTheory
open scoped Topology ENNReal NNReal

noncomputable section
namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩
variable [MeasurableSpace C(PathTime, Sphere)] [BorelSpace C(PathTime, Sphere)]
 theorem continuous_meanIndex_rectangle_witness
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
      (planarSliceBox (Icc a₀ b₀) (Icc c₀ d₀)))
    (hmiss : ∀ z ∈ planarSliceBox (Icc a₀ b₀) (Icc c₀ d₀),
      ∀ᵐ γ : A ∂(η : Measure A), π (z : Sphere) ∉ range γ.val) :
    let W := euclideanPlaneCoordinates ⁻¹' (Ioo a b ×ˢ Ioo c d)
    let v : EuclideanPlane → ℝ := fun p =>
      liftedMeanGeometricIndex hsch K hKS (η.map f) Ψ ⟨p 0, p 1⟩
    ContinuousOn v W ∧
      (∀ p ∈ W, (v p : UnitAddCircle) =
        diskMeanCircle hsch K hKS (η.map f) (F (π ((⟨p 0, p 1⟩ : ℂ) : Sphere)))) ∧
      ∃ H : DeGiorgi.MemW1pWitness 2 v W,
        ∀ i : Fin 2, ∀ᵐ p ∂volume.restrict W,
          |H.weakGrad p i| ≤ (sliceChartDensity B g ⟨p 0, p 1⟩).toReal := by
  let S := planarSliceBox (Icc a₀ b₀) (Icc c₀ d₀)
  let W := euclideanPlaneCoordinates ⁻¹' (Ioo a b ×ˢ Ioo c d)
  let Z : EuclideanPlane → ℂ := fun p => ⟨p 0, p 1⟩
  have hZ : Continuous Z :=
    Complex.equivRealProdCLM.symm.continuous.comp euclideanPlaneCoordinates.continuous
  have hZS : MapsTo Z W S := by
    intro p hp
    exact ⟨⟨ha.le.trans hp.1.1.le, hp.1.2.le.trans hb.le⟩,
      ⟨hc.le.trans hp.2.1.le, hp.2.2.le.trans hd.le⟩⟩
  have hm (z : ℂ) (hz : z ∈ S) :
      ∀ᵐ γ : K ∂((η.map f : ProbabilityMeasure K) : Measure K),
        diskRayProjection (Ψ z) ∉ range γ.val := by
    rw [hproj z hz]
    apply ae_mapped_arc_avoids A K η F f hf hmap _ (hmiss z hz)
    intro γ
    apply (hF γ).mono
    exact union_subset_union Subset.rfl (singleton_subset_iff.mpr ⟨z, hz, rfl⟩)
  have hv := continuousOn_liftedMeanGeometricIndex hsch hsep K hK hKS (η.map f)
    Ψ hΨ hpos hm
  refine ⟨hv.comp hZ.continuousOn hZS, ?_, ?_⟩
  · intro p hp
    exact (diskMeanCircle_eq_local_mean hsch hsep K hK hKS (η.map f)
      (fun z => F (π (z : Sphere))) Ψ (Z p) (hpos _ (hZS hp)) (hproj _ (hZS hp))).symm
  · exact physicalMeanIndex_rectangle_sobolev_witness hsch hsep hcoarea e hU y₀ π hπ he
      A hA η hfinite g hg hocc henergy K hK hKS F f hf hmap
      ha hab hb hc hcd hd hAG B hB Ψ hΨ hpos hproj hF hinj

end CircleDomainRigidity

end

end OAI
