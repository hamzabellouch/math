import Mathlib
import OAI.Geometry.CAT0Fillings.Charts.Jacobian
import OAI.Geometry.CAT0Fillings.Prism.TimeCoordinate
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
lemma prism_action_eq (b : ℝ × X → ℝ) (π : Fin (k+1) → ℝ × X → ℝ)
    (h : Admissible b π) :
    C.prism.action b π =
      ∫ p, (C.multiplicity p.2 : ℝ) * C.scalar (fun x => b (p.1,x)) p.2 *
        C.prism.jacobian π ((Prism.split k).symm p)
          ∂(volume.restrict (Icc (0:ℝ) 1)).prod (volume.restrict C.domain) := by
  rw [action,ite_eq_left h,← C.prism_split_measurePreserving.integral_comp (Prism.split k).symm.toHomeomorph.measurableEmbedding]
  apply integral_congr_ae
  have hp : ∀ᵐ p ∂(volume.restrict (Icc (0:ℝ) 1)).prod (volume.restrict C.domain),
      p ∈ Icc (0:ℝ) 1 ×ˢ C.domain := by
    rw [Measure.prod_restrict]
    exact ae_restrict_mem (measurableSet_Icc.prod C.borel)
  filter_upwards [hp] with p hp
  have hb : C.prism.scalar b ((Prism.split k).symm p) =
      C.scalar (fun x => b (p.1,x)) p.2 := by
    rw [C.prism_scalar_eq hp,C.scalar_eq hp.2]
  rw [hb]
  congr 2

end CAT0Fillings.IntegerChart

namespace CAT0Fillings.IntegerChart
open Set MeasureTheory Filter
open scoped Topology ENNReal NNReal

variable {X : Type*} [MetricSpace X] {k : ℕ} (C : IntegerChart X k)

lemma integrable_prism_formula (b : ℝ × X → ℝ) (π : Fin (k+1) → ℝ × X → ℝ)
    (h : Admissible b π) :
    Integrable (fun p => (C.multiplicity p.2 : ℝ) * C.scalar (fun x => b (p.1,x)) p.2 *
        C.prism.jacobian π ((Prism.split k).symm p))
      ((volume.restrict (Icc (0:ℝ) 1)).prod (volume.restrict C.domain)) := by
  have hi := (C.prism_split_measurePreserving.integrable_comp_emb
    (Prism.split k).symm.toHomeomorph.measurableEmbedding).mpr
      (C.prism.integrable_action_integrand h.1 h.2)
  apply hi.congr
  have hp : ∀ᵐ p ∂(volume.restrict (Icc (0:ℝ) 1)).prod (volume.restrict C.domain),
      p ∈ Icc (0:ℝ) 1 ×ˢ C.domain := by
    rw [Measure.prod_restrict]
    exact ae_restrict_mem (measurableSet_Icc.prod C.borel)
  filter_upwards [hp] with p hp
  have hb : C.prism.scalar b ((Prism.split k).symm p) =
      C.scalar (fun x => b (p.1,x)) p.2 := by
    rw [C.prism_scalar_eq hp,C.scalar_eq hp.2]
  dsimp only [Function.comp_apply]
  rw [hb]
  congr 2

lemma integrable_prism_slice (b : ℝ × X → ℝ) (π : Fin k → ℝ × X → ℝ)
    (h : Admissible b π) :
    Integrable (fun p => (C.multiplicity p.2 : ℝ) * C.scalar (fun x => b (p.1,x)) p.2 *
        C.jacobian (fun i x => π i (p.1,x)) p.2)
      ((volume.restrict (Icc (0:ℝ) 1)).prod (volume.restrict C.domain)) := by
  have hπ : ∀ i, ∃ K : ℝ≥0, LipschitzWith K (Matrix.vecCons Prod.fst π i) :=
    Fin.cases ⟨1,LipschitzWith.prod_fst⟩ h.2
  apply (C.integrable_prism_formula b _ ⟨h.1,hπ⟩).congr
  filter_upwards [C.ae_prism_jacobian_time π h.2] with p hp
  rw [hp]

end CAT0Fillings.IntegerChart
end
end

end OAI
