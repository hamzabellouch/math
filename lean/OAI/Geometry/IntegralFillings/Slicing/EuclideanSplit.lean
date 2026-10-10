import Mathlib
import OAI.Geometry.IntegralFillings.Model

namespace OAI

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

namespace SharpIntegralFillings.Prism
abbrev Euc (k : ℕ) := EuclideanSpace ℝ (Fin k)

noncomputable def splitLinear (k : ℕ) : Euc (k+1) ≃ₗ[ℝ] ℝ × Euc k where
  toFun z := (z 0, WithLp.toLp 2 (fun i => z i.succ))
  invFun p := WithLp.toLp 2 (Matrix.vecCons p.1 (WithLp.ofLp p.2))
  left_inv z := by ext i; exact Fin.cases rfl (fun _ => rfl) i
  right_inv p := by aesop
  map_add' z w := by ext <;> rfl
  map_smul' a z := by ext <;> rfl

noncomputable def split (k : ℕ) : Euc (k+1) ≃L[ℝ] ℝ × Euc k :=
  (splitLinear k).toContinuousLinearEquiv

@[simp] lemma split_apply (k : ℕ) (z : Euc (k+1)) :
    split k z = (z 0, WithLp.toLp 2 (fun i => z i.succ)) := rfl

@[simp] lemma split_symm_apply (k : ℕ) (p : ℝ × Euc k) :
    (split k).symm p = WithLp.toLp 2 (Matrix.vecCons p.1 (WithLp.ofLp p.2)) := rfl

lemma split_measurePreserving (k : ℕ) : MeasurePreserving (split k) := by
  have h := (MeasurePreserving.prod (MeasurePreserving.id (volume : Measure ℝ))
    (PiLp.volume_preserving_toLp (Fin k))).comp
      ((volume_preserving_piFinSuccAbove (fun _ : Fin (k+1) => ℝ) 0).comp
        (PiLp.volume_preserving_ofLp (Fin (k+1))))
  convert h using 1
  · funext z
    apply Prod.ext
    · rfl
    · ext j
      simp [Function.comp_def,MeasurableEquiv.piFinSuccAbove_apply,Fin.tail]

lemma split_symm_measurePreserving (k : ℕ) : MeasurePreserving (split k).symm := by
  exact MeasurePreserving.symm (split k).toHomeomorph.toMeasurableEquiv
    (split_measurePreserving k)

lemma integral_split (k : ℕ) (f : Euc (k+1) → ℝ) :
    ∫ z, f z = ∫ p : ℝ × Euc k, f ((split k).symm p) := by
  exact ((split_symm_measurePreserving k).integral_comp (split k).symm.toHomeomorph.measurableEmbedding f).symm

lemma split_single_zero (k : ℕ) : split k (EuclideanSpace.single 0 1) = (1,0) := by
  ext <;> simp

lemma split_single_succ (k : ℕ) (j : Fin k) :
    split k (EuclideanSpace.single j.succ 1) = (0,EuclideanSpace.single j 1) := by
  ext <;> simp

end SharpIntegralFillings.Prism

end

end OAI
