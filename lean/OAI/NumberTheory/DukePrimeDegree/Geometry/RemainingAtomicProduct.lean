import OAI.NumberTheory.DukePrimeDegree.Geometry.RootPrefixProductKernel
import OAI.NumberTheory.DukePrimeDegree.Geometry.RootPrefixSupport

namespace OAI

/-! # Atomic intrinsic products give actual Dirac conditionals -/

noncomputable section
open MeasureTheory Set
namespace DukePrimeDegree
open PrimeDegreePackets

private lemma pi_real_dirac_zero (ι : Type*) [Fintype ι] :
    Measure.pi (fun _ : ι => Measure.dirac (0:ℝ)) = Measure.dirac (fun _ : ι => (0:ℝ)) := by
  classical
  apply Measure.pi_eq
  intro s _hs
  by_cases h : ∀ i, (0:ℝ) ∈ s i
  · rw [Measure.dirac_apply_of_mem (by simpa only [mem_pi,mem_univ,true_implies] using h)]
    simp only [Measure.dirac_apply_of_mem (h _),Finset.prod_const_one]
  · obtain ⟨i,hi⟩ := not_forall.mp h
    have hnot : (fun _ : ι => (0:ℝ)) ∉ Set.pi univ s := by
      intro ht
      exact hi (ht i (mem_univ i))
    rw [Measure.dirac_apply,Set.indicator_of_notMem hnot]
    exact (Finset.prod_eq_zero (Finset.mem_univ i)
      (by simp only [Measure.dirac_apply,Set.indicator_of_notMem hi])).symm

namespace EliminationChain
variable {n : ℕ} {P : Finset (Fin n × Fin n)} {D : Finset (Fin n)}

theorem remainingIntrinsicProduct_eq_dirac (c : EliminationChain P D)
    (hP : InitialRootPattern P) (hf : c.finalEntries = allPositiveRoots n)
    (μ : Measure (X n)) [IsFiniteMeasure μ] (x : X n)
    (h : ∀ p : ↥(allPositiveRoots n \ P),
      intrinsicRootLeaf (ne_of_lt (Finset.mem_filter.mp (Finset.mem_sdiff.mp p.prop).1).2) μ x =
        Measure.dirac 0) :
    c.remainingIntrinsicProduct hP hf μ x = Measure.dirac 1 := by
  unfold remainingIntrinsicProduct
  simp_rw [h]
  rw [pi_real_dirac_zero,Measure.map_dirac' (c.remainingGroupCoordinates hP hf).symm.measurable]
  congr 1
  apply (c.remainingGroupCoordinates hP hf).injective
  rw [Homeomorph.apply_symm_apply]
  funext p
  rw [c.remainingGroupCoordinates_apply]
  exact (Matrix.one_apply_ne (ne_of_lt (Finset.mem_filter.mp (Finset.mem_sdiff.mp p.prop).1).2)).symm

end EliminationChain

namespace RootPrefixBox
variable {d : ℕ} {P : Finset (Fin (d+1) × Fin (d+1))} {D : Finset (Fin (d+1))}
    {hP : InitialRootPattern P} {c : EliminationChain P D}
    {hf : c.finalEntries = allPositiveRoots (d+1)}
    {T : Type*} [TopologicalSpace T] [SecondCountableTopology T]
    [MeasurableSpace T] [BorelSpace T]
    {C : RootPrefixCoordinates (d+1) P T} {g : G (d+1)}

omit [SecondCountableTopology T] [MeasurableSpace T] [BorelSpace T] in
theorem uncenteredIntrinsicProduct_eq_dirac
    (A : RootPrefixBox C c hP hf g) (μ : Measure (X (d+1))) [IsFiniteMeasure μ]
    (z : (UpperRootTransverse (d+1) × T) × c.Time)
    (h : c.remainingIntrinsicProduct hP hf μ (C.timeParam c hP hf g z) = Measure.dirac 1) :
    A.uncenteredIntrinsicProduct μ z = Measure.dirac z.2 := by
  unfold uncenteredIntrinsicProduct
  rw [h,Measure.map_dirac' (Homeomorph.mulLeft _).measurable,
    Measure.map_dirac' (c.remainingWordHomeomorph hP hf).symm.measurable]
  change Measure.dirac ((c.remainingWordHomeomorph hP hf).symm
    (c.remainingWordHomeomorph hP hf z.2 * 1)) = Measure.dirac z.2
  rw [mul_one,Homeomorph.symm_apply_apply]

omit [SecondCountableTopology T] [MeasurableSpace T] [BorelSpace T] in
theorem intrinsicProductConditional_eq_dirac
    (A : RootPrefixBox C c hP hf g) (μ : Measure (X (d+1))) [IsFiniteMeasure μ]
    (z : (UpperRootTransverse (d+1) × T) × c.Time) (hz : z.2 ∈ A.time)
    (h : c.remainingIntrinsicProduct hP hf μ (C.timeParam c hP hf g z) = Measure.dirac 1) :
    A.intrinsicProductConditional μ z = Measure.dirac z.2 := by
  classical
  rw [intrinsicProductConditional,A.uncenteredIntrinsicProduct_eq_dirac μ z h,anchorNormalize,
    Measure.dirac_apply_of_mem hz,inv_one,one_smul,restrict_dirac,ite_eq_left hz]

theorem ae_conditionalKernel_eq_dirac_of_atomic_roots
    (A : RootPrefixBox C c hP hf g) (R : ℝ) (hAR : A.time ⊆ c.remainingWindow R 0)
    (μ : Measure (X (d+1))) [IsProbabilityMeasure μ]
    [ErgodicSMul (Multiplicative (LogCoordinates d)) (X (d+1)) μ]
    (h : ∀ p : ↥(allPositiveRoots (d+1) \ P), ∀ᵐ x ∂μ,
      intrinsicRootLeaf (ne_of_lt (Finset.mem_filter.mp (Finset.mem_sdiff.mp p.prop).1).2) μ x =
        Measure.dirac 0) :
    ∀ᵐ z ∂A.coordinateMeasure μ, A.conditionalKernel μ z.1 = Measure.dirac z.2 := by
  filter_upwards [A.ae_coordinate_of_ambient μ (ae_all_iff.mpr h),
    A.ae_conditionalKernel_eq_intrinsicProduct R hAR μ,A.coordinateMeasure_ae_domain μ]
    with z hz hk hdom
  exact hk.trans (A.intrinsicProductConditional_eq_dirac μ z hdom.2
    (c.remainingIntrinsicProduct_eq_dirac hP hf μ _ hz))

end RootPrefixBox
end DukePrimeDegree

end

end OAI
