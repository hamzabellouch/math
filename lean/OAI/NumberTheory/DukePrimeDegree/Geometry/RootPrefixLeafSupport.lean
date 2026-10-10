import OAI.NumberTheory.DukePrimeDegree.Geometry.RootPrefixLeafKernel
import OAI.NumberTheory.PrimePackets.KernelSupport

namespace OAI

/-! # Almost every remaining-subgroup leaf coordinate belongs to its measure support -/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology

namespace DukePrimeDegree
open PrimeDegreePackets
namespace RootPrefixBox
variable {n : ℕ} {P : Finset (Fin n × Fin n)} {D : Finset (Fin n)}
    {T : Type*} [TopologicalSpace T] [SecondCountableTopology T]
    [MeasurableSpace T] [BorelSpace T]
    {Pfx : RootPrefixCoordinates n P T} {c : EliminationChain P D}
    {hP : InitialRootPattern P} {hfinal : c.finalEntries = allPositiveRoots n} {g : G n}

theorem ae_mem_leafMeasure_support (A : RootPrefixBox Pfx c hP hfinal g) (R : ℝ)
    (hAR : A.time ⊆ c.remainingWindow R 0)
    (μ : Measure (X n)) [IsFiniteMeasure μ]
    (hfree : ∀ᵐ x ∂μ, ∀ v ∈ positiveRootGeneratedGroup (allPositiveRoots n),
      rightAction x v = x → v = 1) :
    ∀ᵐ z ∂A.coordinateMeasure μ, z.2 ∈ (A.leafMeasure R μ z.1).support := by
  let κ := A.leafKernel R hAR μ hfree
  have H : ∀ᵐ s ∂(A.coordinateMeasure μ).fst, ∀ᵐ t ∂A.conditionalKernel μ s,
      t ∈ (κ s).support := by
    filter_upwards [A.ae_leafMeasure_spec R hAR μ hfree, A.ae_leafKernel_eq R hAR μ hfree]
      with s hs he
    have hle : A.conditionalKernel μ s ≤ κ s := by
      rw [he, ←hs.2.2.1]
      exact Measure.restrict_le_self
    filter_upwards [(A.conditionalKernel μ s).support_mem_ae] with t ht
    exact Measure.support_mono hle ht
  have H' := Measure.ae_compProd_of_ae_ae (measurableSet_kernel_support_secondCountable κ) H
  have hk : ∀ᵐ z ∂A.coordinateMeasure μ, z.2 ∈ (κ z.1).support := by
    simpa only [conditionalKernel, Measure.disintegrate] using H'
  have he : ∀ᵐ z ∂A.coordinateMeasure μ, κ z.1 = A.leafMeasure R μ z.1 :=
    ae_of_ae_map measurable_fst.aemeasurable (A.ae_leafKernel_eq R hAR μ hfree)
  filter_upwards [hk,he] with z hz hez
  rwa [←hez]

theorem ae_leafMeasure_nhds_pos (A : RootPrefixBox Pfx c hP hfinal g) (R : ℝ)
    (hAR : A.time ⊆ c.remainingWindow R 0)
    (μ : Measure (X n)) [IsFiniteMeasure μ]
    (hfree : ∀ᵐ x ∂μ, ∀ v ∈ positiveRootGeneratedGroup (allPositiveRoots n),
      rightAction x v = x → v = 1) :
    ∀ᵐ z ∂A.coordinateMeasure μ, ∀ U ∈ 𝓝 z.2, 0 < A.leafMeasure R μ z.1 U := by
  filter_upwards [A.ae_mem_leafMeasure_support R hAR μ hfree] with z hz
  exact (A.leafMeasure R μ z.1).mem_support_iff_forall z.2 |>.mp hz

end RootPrefixBox
end DukePrimeDegree

end

end OAI
