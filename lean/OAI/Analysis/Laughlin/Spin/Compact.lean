import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Algebra.Star.Unitary
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.MetricSpace.ProperSpace
import OAI.Analysis.Laughlin.Spin.TensorAction

namespace OAI

namespace Laughlin.Rotation
open scoped BigOperators Matrix

instance sourceSU2_continuousInv : ContinuousInv SourceSU2 where
  continuous_inv := by
    apply continuous_induced_rng.mpr
    change Continuous (fun g : SourceSU2 => (g.val)ᴴ)
    fun_prop

instance sourceSU2_topologicalGroup : IsTopologicalGroup SourceSU2 where

 theorem unitary_entry_norm_le_one (A : Matrix (Fin 2) (Fin 2) ℂ)
    (hA : A ∈ Matrix.unitaryGroup (Fin 2) ℂ) (i j : Fin 2) : ‖A i j‖ ≤ 1 := by
  have h := congrFun (congrFun (Matrix.mem_unitaryGroup_iff.mp hA) i) i
  rw [Matrix.star_eq_conjTranspose] at h
  have hs : ∑ k, ‖A i k‖^2 = (1 : ℝ) := by
    have hr := congrArg Complex.re h
    simpa [Matrix.mul_apply,Matrix.conjTranspose_apply,Complex.mul_conj,Complex.normSq_eq_norm_sq,← Complex.ofReal_pow] using hr
  have hj : ‖A i j‖^2 ≤ ∑ k, ‖A i k‖^2 :=
    Finset.single_le_sum (fun k hk => sq_nonneg ‖A i k‖) (Finset.mem_univ j)
  rw [hs] at hj
  nlinarith [norm_nonneg (A i j)]

 theorem sourceSU2_isClosed :
    IsClosed (Matrix.specialUnitaryGroup (Fin 2) ℂ : Set (Matrix (Fin 2) (Fin 2) ℂ)) := by
  have he : (Matrix.specialUnitaryGroup (Fin 2) ℂ : Set (Matrix (Fin 2) (Fin 2) ℂ)) =
      (unitary (Matrix (Fin 2) (Fin 2) ℂ) : Set _) ∩ {A | A.det=1} := rfl
  rw [he]
  exact isClosed_unitary.inter (isClosed_eq (by fun_prop) continuous_const)

 theorem sourceSU2_isCompact :
    IsCompact (Matrix.specialUnitaryGroup (Fin 2) ℂ : Set (Matrix (Fin 2) (Fin 2) ℂ)) := by
  let K : Set (Matrix (Fin 2) (Fin 2) ℂ) :=
    {A | ∀ i j, A i j ∈ Metric.closedBall (0 : ℂ) 1}
  have hK : IsCompact K := by
    exact isCompact_pi_infinite (fun i : Fin 2 =>
      isCompact_pi_infinite (fun j : Fin 2 => isCompact_closedBall (0 : ℂ) 1))
  apply hK.of_isClosed_subset sourceSU2_isClosed
  intro A hA i j
  simp only [Metric.mem_closedBall,dist_zero_right]
  exact unitary_entry_norm_le_one A hA.1 i j

instance sourceSU2_compactSpace : CompactSpace SourceSU2 :=
  isCompact_iff_compactSpace.mp sourceSU2_isCompact

 theorem sourceTensorRepresentation_continuous (Q : ℕ) (a b : Fin Q → Fin 2) :
    Continuous (fun g : SourceSU2 => sourceTensorRepresentation Q g a b) := by
  change Continuous (fun g : SourceSU2 => ∏ i, g.val (a i) (b i))
  exact continuous_finsetProd _ (fun i hi => (continuous_apply (b i)).comp
    ((continuous_apply (a i)).comp continuous_subtype_val))

end Laughlin.Rotation

end OAI
