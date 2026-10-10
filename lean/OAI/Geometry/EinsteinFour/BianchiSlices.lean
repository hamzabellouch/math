import OAI.Geometry.EinsteinFour.HighestProjection

namespace OAI

/-! Actual gradient slices of a four-slot Hessian. -/

namespace PositiveEinsteinFour.HighestHessian

noncomputable section

open scoped BigOperators
open Bianchi TraceHessian

/-- A fixed outer derivative, retaining its actual tangent-vector entries. -/
def innerSlice (X : Hessian) (i : Fin 4) : Tensor where
  diagonal a := WithLp.toLp 2 (fun j => X i j a a)
  off a := WithLp.toLp 2 (fun j => X i j (next a) (previous a))

theorem innerSlice_matrix (X : Hessian) (i : Fin 4)
    (hs : ∀ j, symmetric (X i j)) (a b : Fin 3) :
    (innerSlice X i).matrix a b = WithLp.toLp 2 (fun j => X i j a b) := by
  ext j
  fin_cases a <;> fin_cases b <;> simp [innerSlice, Tensor.matrix, next, previous]
  all_goals exact hs j _ _

theorem innerSlice_traceFree (X : Hessian) (i : Fin 4)
    (ht : ∀ j, traceFree (X i j)) : (innerSlice X i).traceFree := by
  ext j
  simpa [Tensor.traceFree, innerSlice, traceFree, Fin.sum_univ_three] using ht j

theorem innerSlice_bianchi (X : Hessian) (i : Fin 4)
    (hs : ∀ j, symmetric (X i j)) (hb : ∀ r, divergence X i r = 0) :
    (innerSlice X i).bianchi := by
  intro r
  rw [Tensor.divergence_eq_sum]
  simp_rw [innerSlice_matrix X i hs]
  exact hb r

/-- The concrete highest-Hessian constraints give genuine Bianchi slices. -/
theorem innerSlice_of_condition (X : Hessian) (hX : condition X) (i : Fin 4) :
    (innerSlice X i).traceFree ∧ (innerSlice X i).bianchi := by
  exact ⟨innerSlice_traceFree X i (fun j => (hX.2.1 i j).2),
    innerSlice_bianchi X i (fun j => (hX.2.1 i j).1) (hX.2.2.2 i)⟩

end
end PositiveEinsteinFour.HighestHessian

end OAI
