import OAI.NumberTheory.DukePrimeDegree.Geometry.RootPrefixLocalRestriction

namespace OAI

/-! # Prefix-box kernels are normalized restrictions of surrounding kernels -/

noncomputable section
open MeasureTheory ProbabilityTheory Set
namespace DukePrimeDegree
open PrimeDegreePackets
namespace RootPrefixBox
variable {n : ℕ} {P : Finset (Fin n × Fin n)} {D : Finset (Fin n)}
    {T : Type*} [TopologicalSpace T] [MeasurableSpace T] [BorelSpace T]
    {Pfx : RootPrefixCoordinates n P T} {c : EliminationChain P D}
    {hP : InitialRootPattern P} {hfinal : c.finalEntries = allPositiveRoots n} {g : G n}

theorem conditional_of_restrict_eq (B : RootPrefixBox Pfx c hP hfinal g)
    (μ : Measure (X n)) [IsFiniteMeasure μ]
    (σ : Measure ((UpperRootTransverse n × T) × c.Time)) [IsFiniteMeasure σ]
    (hres : σ.restrict B.domain = B.coordinateMeasure μ) :
    ∀ᵐ s ∂(B.coordinateMeasure μ).fst,
      σ.condKernel s B.time ≠ 0 ∧ B.conditionalKernel μ s =
        (anchorNormalize (σ.condKernel s) B.time).restrict B.time := by
  have H := conditional_restrict_normalized σ B.domain
    (B.transverse_open.prod B.time_open).measurableSet
  have H' : ∀ᵐ s ∂(B.coordinateMeasure μ).fst,
      σ.condKernel s (Prod.mk s ⁻¹' B.domain) ≠ 0 ∧ B.conditionalKernel μ s =
        (anchorNormalize (σ.condKernel s) (Prod.mk s ⁻¹' B.domain)).restrict
          (Prod.mk s ⁻¹' B.domain) := by
    simpa only [hres,conditionalKernel] using H
  filter_upwards [H',B.coordinateMeasure_fst_ae_transverse μ] with s hs hst
  have he : Prod.mk s ⁻¹' B.domain = B.time := by
    ext t
    simp only [Set.mem_preimage,Set.mem_prod,hst,true_and]
  simpa only [he] using hs

theorem conditional_on_overlap (B : RootPrefixBox Pfx c hP hfinal g)
    (μ : Measure (X n)) [IsFiniteMeasure μ]
    (σ : Measure ((UpperRootTransverse n × T) × c.Time)) [IsFiniteMeasure σ]
    (U : Set ((UpperRootTransverse n × T) × c.Time)) (hU : MeasurableSet U)
    (hres : σ.restrict B.domain = (B.coordinateMeasure μ).restrict U) :
    ∀ᵐ s ∂(σ.restrict B.domain).fst,
      σ.condKernel s B.time ≠ 0 ∧
      B.conditionalKernel μ s (Prod.mk s ⁻¹' U) ≠ 0 ∧
      (anchorNormalize (σ.condKernel s) B.time).restrict B.time =
        (anchorNormalize (B.conditionalKernel μ s) (Prod.mk s ⁻¹' U)).restrict
          (Prod.mk s ⁻¹' U) := by
  have Hσ := conditional_restrict_normalized σ B.domain
    (B.transverse_open.prod B.time_open).measurableSet
  have HB := conditional_restrict_normalized (B.coordinateMeasure μ) U hU
  have HB' : ∀ᵐ s ∂(σ.restrict B.domain).fst,
      B.conditionalKernel μ s (Prod.mk s ⁻¹' U) ≠ 0 ∧
      (σ.restrict B.domain).condKernel s =
        (anchorNormalize (B.conditionalKernel μ s) (Prod.mk s ⁻¹' U)).restrict
          (Prod.mk s ⁻¹' U) := by
    simpa only [hres,conditionalKernel] using HB
  have hdom : ∀ᵐ z ∂σ.restrict B.domain, z ∈ B.domain :=
    ae_restrict_mem (B.transverse_open.prod B.time_open).measurableSet
  have hbase : ∀ᵐ s ∂(σ.restrict B.domain).fst, s ∈ B.transverse := by
    apply (ae_map_iff measurable_fst.aemeasurable B.transverse_open.measurableSet).mpr
    exact hdom.mono fun _ hz => hz.1
  filter_upwards [Hσ,HB',hbase] with s hs hb hst
  have he : Prod.mk s ⁻¹' B.domain = B.time := by
    ext t
    simp only [Set.mem_preimage,Set.mem_prod,hst,true_and]
  rw [he] at hs
  exact ⟨hs.1,hb.1,hs.2.symm.trans hb.2⟩

end RootPrefixBox
end DukePrimeDegree

end

end OAI
