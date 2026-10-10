import Mathlib
import OAI.Geometry.CAT0Fillings.Charts.Differentiability
import OAI.Geometry.CAT0Fillings.Prism.Differential
import OAI.Geometry.CAT0Fillings.Slicing.EuclideanSplit

namespace OAI

section
section
open Filter Set
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open Set MeasureTheory
open scoped RealInnerProductSpace
open Matrix
open scoped RealInnerProductSpace MatrixOrder
open Set Filter MeasureTheory
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal
open Set MeasureTheory Measure Filter Module
open Set Filter MeasureTheory Measure ContinuousLinearMap
open scoped Topology Convolution NNReal
open Set Filter MeasureTheory Measure Metric
open scoped Topology ContDiff
open Set Filter Metric
open scoped Topology NNReal
open Set MeasureTheory Filter
open scoped Topology ENNReal NNReal

namespace CAT0Fillings.IntegerChart
open Set MeasureTheory Filter
open scoped Topology ENNReal NNReal

variable {X : Type*} [MetricSpace X] {k : ℕ} (C : IntegerChart X k)
lemma ae_prism_fderiv_time :
    ∀ᵐ z ∂volume.restrict C.prism.domain,
      fderivWithin ℝ (C.prism.scalar Prod.fst) C.prism.domain z =
        (ContinuousLinearMap.fst ℝ ℝ (Euc k)).comp (Prism.split k).toContinuousLinearMap := by
  filter_upwards [ae_uniqueDiffWithinAt volume C.prism.domain,
    ae_restrict_mem (μ := volume) C.prism.borel] with z hu hz
  let F : Euc (k+1) →L[ℝ] ℝ :=
    (ContinuousLinearMap.fst ℝ ℝ (Euc k)).comp (Prism.split k).toContinuousLinearMap
  have heq : EqOn (C.prism.scalar Prod.fst) F C.prism.domain := by
    intro w hw
    rw [C.prism.scalar_eq hw]
    rfl
  rw [fderivWithin_congr' heq hz]
  exact F.fderivWithin hu

lemma ae_prism_jacobian_time (π : Fin k → ℝ × X → ℝ)
    (hπ : ∀ i, ∃ K : ℝ≥0, LipschitzWith K (π i)) :
    ∀ᵐ p ∂(volume.restrict (Icc (0:ℝ) 1)).prod (volume.restrict C.domain),
      C.prism.jacobian (Matrix.vecCons Prod.fst π) ((Prism.split k).symm p) =
        C.jacobian (fun i x => π i (p.1,x)) p.2 := by
  have htime := C.prism_split_measurePreserving.quasiMeasurePreserving.ae C.ae_prism_fderiv_time
  have hcoord := ae_all_iff.mpr fun i => C.ae_prism_fderiv_decompose (hπ i).choose_spec
  filter_upwards [htime,hcoord] with p ht hp
  change Matrix.det (Matrix.of (fun i j =>
    (fderivWithin ℝ (C.prism.scalar (Matrix.vecCons Prod.fst π i)) C.prism.domain
      ((Prism.split k).symm p)) (EuclideanSpace.single j 1))) = _
  rw [Matrix.det_succ_row_zero]
  have hrow (j : Fin (k+1)) :
      (fderivWithin ℝ (C.prism.scalar Prod.fst) C.prism.domain ((Prism.split k).symm p))
        (EuclideanSpace.single j 1) = if j = 0 then 1 else 0 := by
    rw [ht]
    induction j using Fin.cases with
    | zero => simp [ContinuousLinearMap.comp_apply]
    | succ j => simp [ContinuousLinearMap.comp_apply]
  simp only [Matrix.of_apply,Matrix.cons_val_zero,hrow]
  simp only [mul_ite,mul_zero,ite_mul,zero_mul,Finset.sum_ite_eq',Finset.mem_univ,ite_true,
    Fin.val_zero,pow_zero,one_mul]
  apply congrArg Matrix.det
  ext i j
  simpa only [Matrix.submatrix_apply,Matrix.of_apply,Fin.succAbove_zero,Matrix.cons_val_succ]
    using (hp i).2 j

lemma lipschitz_time {f : ℝ × X → ℝ} {K : ℝ≥0} (hf : LipschitzWith K f) (x : X) :
    LipschitzWith K (fun t => f (t,x)) := by
  simpa [Function.comp_def] using hf.comp ((LipschitzWith.id : LipschitzWith 1 (id : ℝ → ℝ)).prodMk
    (LipschitzWith.const x))

lemma lipschitz_slice {f : ℝ × X → ℝ} {K : ℝ≥0} (hf : LipschitzWith K f) (t : ℝ) :
    LipschitzWith K (fun x => f (t,x)) := by
  simpa [Function.comp_def] using hf.comp ((LipschitzWith.const t).prodMk
    (LipschitzWith.id : LipschitzWith 1 (id : X → X)))

lemma boundedLip_slice {b : ℝ × X → ℝ} (hb : BoundedLip b) (t : ℝ) :
    BoundedLip (fun x => b (t,x)) :=
  ⟨⟨_,lipschitz_slice hb.1.choose_spec t⟩,hb.2.choose,fun x => hb.2.choose_spec (t,x)⟩

end CAT0Fillings.IntegerChart
end
end

end OAI
