import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.Connected.TotallyDisconnected
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Measure.OpenPos

namespace OAI

/-!
# From regularity and finite derivative labels to an affine profile

A continuous derivative taking only finitely many values is constant on a
connected domain, and the profile is globally affine.
-/

namespace PolycyclicRecognition

/-- A continuous map from a connected space into a finite subset is constant. -/
theorem eq_of_continuous_finite_range
    {X Y : Type*} [TopologicalSpace X] [PreconnectedSpace X]
    [TopologicalSpace Y] [T1Space Y]
    (f : X → Y) (hf : Continuous f) (hfinite : Set.Finite (Set.range f)) (x y : X) :
    f x = f y := by
  exact isPreconnected_univ.constant_of_mapsTo hfinite.isDiscrete hf.continuousOn
    (fun z _ => Set.mem_range_self z) (Set.mem_univ x) (Set.mem_univ y)

/-- A regular profile whose derivatives lie in a finite set has one global
linear label. The offset is its value at the identity of the vector space. -/
theorem affine_of_continuous_finite_derivative
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : E → F) (A : E → E →L[ℝ] F)
    (hderiv : ∀ x, HasFDerivAt f (A x) x)
    (hcontinuous : Continuous A) (hfinite : Set.Finite (Set.range A)) :
    ∀ x, f x = f 0 + A 0 x := by
  have hA (x : E) : A x = A 0 := eq_of_continuous_finite_range A hcontinuous hfinite x 0
  let g : E → F := fun x => f 0 + A 0 x
  have hg (x : E) : HasFDerivAt g (A 0) x := by
    exact (A 0).hasFDerivAt.const_add (f 0)
  have heq : f = g := by
    apply eq_of_fderiv_eq (fun x => (hderiv x).differentiableAt)
      (fun x => (hg x).differentiableAt) (x := (0 : E))
    · intro x
      rw [(hderiv x).fderiv, (hg x).fderiv, hA]
    · simp [g]
  intro x
  exact congrFun heq x

/-- For a measure positive on open sets, a continuous map lying in a closed
set almost everywhere lies there everywhere. -/
theorem mem_closed_of_continuous_ae
    {X Y : Type*} [TopologicalSpace X] [MeasurableSpace X]
    [TopologicalSpace Y] [T2Space Y]
    (μ : MeasureTheory.Measure X) [MeasureTheory.Measure.IsOpenPosMeasure μ]
    (f : X → Y) (hf : Continuous f) (S : Set Y) (hS : IsClosed S)
    (hae : ∀ᵐ x ∂μ, f x ∈ S) : ∀ x, f x ∈ S := by
  have hc : IsClosed (f ⁻¹' S) := hS.preimage hf
  have heq : f ⁻¹' S = Set.univ := hc.ae_eq_univ_iff_eq.mp (by
    filter_upwards [hae] with x hx
    simp only [Set.mem_preimage, Set.mem_univ, hx])
  intro x
  have hx : x ∈ f ⁻¹' S := heq ▸ Set.mem_univ x
  exact hx

/-- The almost-everywhere finite-label condition obtained by profile volume
comparison suffices after regularity has supplied a continuous derivative. -/
theorem affine_of_contDiff_ae_finite_derivative
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (μ : MeasureTheory.Measure E) [MeasureTheory.Measure.IsOpenPosMeasure μ]
    (f : E → F) (hf : ContDiff ℝ 1 f)
    (S : Set (E →L[ℝ] F)) (hS : S.Finite)
    (hae : ∀ᵐ x ∂μ, fderiv ℝ f x ∈ S) :
    ∀ x, f x = f 0 + fderiv ℝ f 0 x := by
  have hc : Continuous (fderiv ℝ f) := hf.continuous_fderiv (by norm_num)
  have hall := mem_closed_of_continuous_ae μ (fderiv ℝ f) hc S hS.isClosed hae
  have hfinite : Set.Finite (Set.range (fderiv ℝ f)) := hS.subset (by
    rintro _ ⟨x, rfl⟩
    exact hall x)
  exact affine_of_continuous_finite_derivative f (fderiv ℝ f)
    (fun x => (hf.differentiable_one x).hasFDerivAt) hc hfinite

end PolycyclicRecognition

end OAI
