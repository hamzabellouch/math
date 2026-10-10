import OAI.NumberTheory.DukePrimeDegree.Geometry.UpperRootNormalizedLeaves

namespace OAI

/-!
# Measurable full upper-root leaf kernels

The chosen leaf measure is measurable almost everywhere because its
restrictions to the countable exhausting windows are actual normalized
conditional kernels. This supplies a measurable kernel for integration.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal Topology

namespace DukePrimeDegree
open PrimeDegreePackets
namespace UpperRootBox
variable {n : ℕ} {g : G n}

lemma aemeasurable_leafMeasure_restrict_window (A : UpperRootBox n g) (R : ℝ)
    (hAR : A.time ⊆ upperRootWindow n R 0)
    (μ : Measure (X n)) [IsFiniteMeasure μ]
    (hfree : ∀ᵐ x ∂μ, ∀ v ∈ positiveRootGeneratedGroup (allPositiveRoots n),
      rightAction x v = x → v = 1)
    (m : ℕ) :
    AEMeasurable (fun s => (A.leafMeasure R μ s).restrict (upperRootWindow n R m))
      (A.coordinateMeasure μ).fst := by
  let C := upperRootLongBoxFamily n g R
  let : Countable (C m) := (upperRootLongBoxFamily_countable n g R m).to_subtype
  let U := ⋃ B : C m, B.val.transverse
  have hU : ∀ᵐ s ∂(A.coordinateMeasure μ).fst, s ∈ U := by
    filter_upwards [A.ae_injective_upperRoot_slice_of_ae_free μ hfree] with s hs
    obtain ⟨B,hB,hsB⟩ := upperRootLongBoxFamily_covers n g R m s hs
    exact mem_iUnion.mpr ⟨⟨B,hB⟩,hsB⟩
  have H : AEMeasurable (fun s => (A.leafMeasure R μ s).restrict (upperRootWindow n R m))
      ((A.coordinateMeasure μ).fst.restrict U) := by
    apply aemeasurable_iUnion_iff.mpr
    intro B
    have hM : Measurable (fun s =>
        (anchorNormalize (B.val.conditionalKernel μ s) A.time).restrict (upperRootWindow n R m)) := by
      apply Measure.measurable_of_measurable_coe
      intro T hT
      simp only [Measure.restrict_apply hT,anchorNormalize,Measure.smul_apply,smul_eq_mul]
      exact ((B.val.conditionalKernel μ).measurable_coe A.time_open.measurableSet).inv.mul
        ((B.val.conditionalKernel μ).measurable_coe (hT.inter (upperRootWindow_open n R m).measurableSet))
    apply hM.aemeasurable.congr
    change ∀ᵐ s ∂(A.coordinateMeasure μ).fst.restrict B.val.transverse, _
    rw [ae_restrict_iff' B.val.transverse_open.measurableSet]
    filter_upwards [A.ae_leafMeasure_spec R hAR μ hfree] with s hs
    intro hsB
    exact (hs.2.2.2 m B.val B.prop hsB).symm
  simpa only [Measure.restrict_eq_self_of_ae_mem hU] using H



theorem aemeasurable_leafMeasure (A : UpperRootBox n g) (R : ℝ)
    (hAR : A.time ⊆ upperRootWindow n R 0)
    (μ : Measure (X n)) [IsFiniteMeasure μ]
    (hfree : ∀ᵐ x ∂μ, ∀ v ∈ positiveRootGeneratedGroup (allPositiveRoots n),
      rightAction x v = x → v = 1) :
    AEMeasurable (A.leafMeasure R μ) (A.coordinateMeasure μ).fst := by
  let W := upperRootWindow n R
  let V := disjointed W
  have hV (m : ℕ) : MeasurableSet (V m) :=
    MeasurableSet.disjointed (fun m => (upperRootWindow_open n R m).measurableSet) m
  have hM (m : ℕ) : AEMeasurable
      (fun s => (A.leafMeasure R μ s).restrict (V m)) (A.coordinateMeasure μ).fst := by
    have H := (measurable_measure_restrict (hV m)).comp_aemeasurable
      (A.aemeasurable_leafMeasure_restrict_window R hAR μ hfree m)
    change AEMeasurable (fun s => ((A.leafMeasure R μ s).restrict (W m)).restrict (V m))
      (A.coordinateMeasure μ).fst at H
    have hVW : V m ∩ W m = V m := inter_eq_left.mpr (disjointed_subset W m)
    simpa only [Measure.restrict_restrict (hV m),hVW] using H
  have hE (s : UpperRootTransverse n) : A.leafMeasure R μ s =
      Measure.sum (fun m => (A.leafMeasure R μ s).restrict (V m)) := by
    exact measure_eq_sum_disjointed (A.leafMeasure R μ s) W
      (fun m => (upperRootWindow_open n R m).measurableSet) (upperRootWindow_cover n R)
  exact (measurable_measure_sum.comp_aemeasurable (aemeasurable_pi_iff.mpr hM)).congr
    (ae_of_all _ fun s => (hE s).symm)



def leafKernel (A : UpperRootBox n g) (R : ℝ)
    (hAR : A.time ⊆ upperRootWindow n R 0)
    (μ : Measure (X n)) [IsFiniteMeasure μ]
    (hfree : ∀ᵐ x ∂μ, ∀ v ∈ positiveRootGeneratedGroup (allPositiveRoots n),
      rightAction x v = x → v = 1) :
    Kernel (UpperRootTransverse n) (UpperRootTime n) where
  toFun := (A.aemeasurable_leafMeasure R hAR μ hfree).mk (A.leafMeasure R μ)
  measurable' := (A.aemeasurable_leafMeasure R hAR μ hfree).measurable_mk

lemma ae_leafKernel_eq (A : UpperRootBox n g) (R : ℝ)
    (hAR : A.time ⊆ upperRootWindow n R 0)
    (μ : Measure (X n)) [IsFiniteMeasure μ]
    (hfree : ∀ᵐ x ∂μ, ∀ v ∈ positiveRootGeneratedGroup (allPositiveRoots n),
      rightAction x v = x → v = 1) :
    ∀ᵐ s ∂(A.coordinateMeasure μ).fst,
      A.leafKernel R hAR μ hfree s = A.leafMeasure R μ s :=
  (A.aemeasurable_leafMeasure R hAR μ hfree).ae_eq_mk.symm


end UpperRootBox
end DukePrimeDegree

end

end OAI
