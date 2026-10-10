import OAI.NumberTheory.TwoPoint.Bounds.MatrixSpectralTail
import Mathlib.Topology.Algebra.Module.Spaces.ContinuousLinearMap

namespace OAI

/-! Identify the concrete nonbacktracking matrix with the operator in
the spectral transfer lemma. The change of norm is by conjugacy. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

variable {D V : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]

noncomputable def blockEuclideanEquiv :
    (D → EuclideanSpace ℂ V) ≃L[ℂ] EuclideanSpace ℂ (D × V) :=
  LinearEquiv.toContinuousLinearEquiv
    { toFun := fun v => WithLp.toLp 2 (fun x => v x.1 x.2)
      invFun := fun v d => WithLp.toLp 2 (fun i => v (d, i))
      left_inv := by intro v; ext d i; rfl
      right_inv := by intro v; ext x; rfl
      map_add' := by intro v w; ext x; rfl
      map_smul' := by intro c v; ext x; rfl }

omit [DecidableEq D] [DecidableEq V] in
lemma blockEuclideanEquiv_apply (v : D → EuclideanSpace ℂ V) (d : D) (i : V) :
    blockEuclideanEquiv v (d, i) = v d i := rfl

omit [DecidableEq D] [DecidableEq V] in
lemma blockEuclideanEquiv_symm_apply (v : EuclideanSpace ℂ (D × V)) (d : D) (i : V) :
    blockEuclideanEquiv.symm v d i = v (d, i) := rfl

lemma blockNonbacktracking_operator_conj (A : D → Matrix V V ℝ) :
    blockEuclideanEquiv.conjContinuousAlgEquiv
      (nonbacktrackingContinuous (fun d => matrixOperator (fun i j => (A d i j : ℂ)))) =
      matrixOperator (fun i j => (blockNonbacktrackingMatrix A i j : ℂ)) := by
  ext v x
  rcases x with ⟨d, i⟩
  rw [ContinuousLinearEquiv.conjContinuousAlgEquiv_apply_apply, blockEuclideanEquiv_apply]
  change (∑ l ∈ univ.erase d, matrixOperator (fun i j => (A l i j : ℂ))
    (blockEuclideanEquiv.symm v l)) i = _
  simp only [WithLp.ofLp_sum, Finset.sum_apply, matrixOperator_apply,
    blockEuclideanEquiv_symm_apply]
  rw [Fintype.sum_prod_type]
  calc
    _ = ∑ l : D, if d ≠ l then ∑ j : V, (A l i j : ℂ) * v (l, j) else 0 := by
      have he : univ.erase d = univ.filter (fun l : D => d ≠ l) := by
        ext l
        simp [ne_comm]
      rw [he, sum_filter]
    _ = _ := by
      apply sum_congr rfl
      intro l _
      by_cases hd : d ≠ l <;> simp [blockNonbacktrackingMatrix, hd]

theorem blockNonbacktracking_spectralRadius (A : D → Matrix V V ℝ) :
    spectralRadius ℂ
      (nonbacktrackingContinuous (fun d => matrixOperator (fun i j => (A d i j : ℂ)))) =
      spectralRadius ℂ (matrixOperator (fun i j => (blockNonbacktrackingMatrix A i j : ℂ))) := by
  let e := (blockEuclideanEquiv (D := D) (V := V)).conjContinuousAlgEquiv
  have hs := AlgEquiv.spectrum_eq e
    (nonbacktrackingContinuous (fun d => matrixOperator (fun i j => (A d i j : ℂ))))
  rw [blockNonbacktracking_operator_conj] at hs
  simp only [spectralRadius_eq_of_unital, hs]

end TwoPointCorrelations

end OAI
