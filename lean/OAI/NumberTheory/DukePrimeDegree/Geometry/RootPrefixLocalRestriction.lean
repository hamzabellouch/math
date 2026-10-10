import OAI.NumberTheory.DukePrimeDegree.Geometry.RootPrefixRestrictions
import OAI.NumberTheory.DukePrimeDegree.Geometry.RootPrefixCompatibility

namespace OAI

/-! # Recovering prefix-box kernels from a larger open coordinate region -/

noncomputable section
open MeasureTheory Set
namespace DukePrimeDegree
open PrimeDegreePackets
namespace RootPrefixBox
variable {n : ℕ} {P : Finset (Fin n × Fin n)} {D : Finset (Fin n)}
    {T : Type*} [TopologicalSpace T] [MeasurableSpace T] [BorelSpace T]
    {Pfx : RootPrefixCoordinates n P T} {c : EliminationChain P D}
    {hP : InitialRootPattern P} {hfinal : c.finalEntries = allPositiveRoots n} {g : G n}

theorem restrict_box_eq_coordinateMeasure_restrict
    (B : RootPrefixBox Pfx c hP hfinal g)
    (U : Set ((UpperRootTransverse n × T) × c.Time)) (hU : IsOpen U)
    (he : Topology.IsOpenEmbedding (U.domRestrict (Pfx.timeParam c hP hfinal g)))
    (μ : Measure (X n)) (σ : Measure ((UpperRootTransverse n × T) × c.Time))
    (hsupport : ∀ᵐ z ∂σ, z ∈ U)
    (hmap : σ.map (Pfx.timeParam c hP hfinal g) =
      μ.restrict (Pfx.timeParam c hP hfinal g '' U)) :
    σ.restrict B.domain = (B.coordinateMeasure μ).restrict U := by
  let f := Pfx.timeParam c hP hfinal g
  let e := U.domRestrict f
  let σU := σ.comap (Subtype.val : U → (UpperRootTransverse n × T) × c.Time)
  have hf : Measurable f := (Pfx.timeParam_localHomeomorph c hP hfinal g).continuous.measurable
  have hv : σU.map Subtype.val = σ := by
    rw [map_comap_subtype_coe hU.measurableSet,
      Measure.restrict_eq_self_of_ae_mem hsupport]
  have hr : Set.range e = f '' U := by
    ext x
    constructor
    · rintro ⟨z,rfl⟩
      exact ⟨z.val,z.prop,rfl⟩
    · rintro ⟨z,hz,rfl⟩
      exact ⟨⟨z,hz⟩,rfl⟩
  have hσU : σU = μ.comap e := by
    apply he.measurableEmbedding.map_injective
    calc
      σU.map e = (σU.map Subtype.val).map f := by
        rw [Measure.map_map hf measurable_subtype_coe]
        rfl
      _ = σ.map f := by rw [hv]
      _ = μ.restrict (f '' U) := hmap
      _ = (μ.comap e).map e := by rw [he.measurableEmbedding.map_comap,hr]
  have hσ : σ = (μ.comap e).map Subtype.val := by rw [←hv,hσU]
  ext S hS
  rw [Measure.restrict_apply hS,hσ,Measure.map_apply measurable_subtype_coe
    (hS.inter (B.transverse_open.prod B.time_open).measurableSet),
    he.measurableEmbedding.comap_apply,Measure.restrict_apply hS,
    B.coordinateMeasure_apply μ (hS.inter hU.measurableSet)]
  congr 1
  ext x
  constructor
  · rintro ⟨z,hz,rfl⟩
    exact ⟨z.val,⟨⟨hz.1,z.prop⟩,hz.2⟩,rfl⟩
  · rintro ⟨z,⟨⟨hzS,hzU⟩,hzB⟩,rfl⟩
    exact ⟨⟨z,hzU⟩,⟨hzS,hzB⟩,rfl⟩


theorem restrict_eq_coordinateMeasure
    (B : RootPrefixBox Pfx c hP hfinal g)
    (U : Set ((UpperRootTransverse n × T) × c.Time)) (hU : IsOpen U)
    (he : Topology.IsOpenEmbedding (U.domRestrict (Pfx.timeParam c hP hfinal g)))
    (hBU : B.domain ⊆ U)
    (μ : Measure (X n)) (σ : Measure ((UpperRootTransverse n × T) × c.Time))
    (hsupport : ∀ᵐ z ∂σ, z ∈ U)
    (hmap : σ.map (Pfx.timeParam c hP hfinal g) =
      μ.restrict (Pfx.timeParam c hP hfinal g '' U)) :
    σ.restrict B.domain = B.coordinateMeasure μ := by
  rw [B.restrict_box_eq_coordinateMeasure_restrict U hU he μ σ hsupport hmap]
  exact Measure.restrict_eq_self_of_ae_mem
    ((B.coordinateMeasure_ae_domain μ).mono fun _ hz => hBU hz)

end RootPrefixBox
end DukePrimeDegree

end

end OAI
