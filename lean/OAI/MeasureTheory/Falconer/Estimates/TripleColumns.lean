import OAI.MeasureTheory.Falconer.Geometry.EuclideanCross
import Mathlib.Topology.Algebra.Module.FiniteDimension

namespace OAI

/-! # Explicit cofactor coordinates for three transverse directions -/

namespace Falconer
open scoped BigOperators

noncomputable def tripleCofactors (u v w : Space 3) : Fin 3 → Space 3 :=
  ![euclideanCross v w,euclideanCross w u,euclideanCross u v]

theorem tripleCofactors_inner (u v w : Space 3) (i j : Fin 3) :
    inner ℝ (tripleCofactors u v w i) (![u,v,w] j) =
      if i = j then inner ℝ u (euclideanCross v w) else 0 := by
  have h0 : inner ℝ (euclideanCross v w) u = inner ℝ u (euclideanCross v w) := real_inner_comm _ _
  have h1 : inner ℝ (euclideanCross w u) v = inner ℝ u (euclideanCross v w) :=
    (real_inner_comm _ _).trans (euclideanCross_cyclic u v w).symm
  have h2 : inner ℝ (euclideanCross u v) w = inner ℝ u (euclideanCross v w) :=
    (real_inner_comm _ _).trans ((euclideanCross_cyclic v w u).symm.trans
      (euclideanCross_cyclic u v w).symm)
  have hz₁ (a b : Space 3) : inner ℝ (euclideanCross a b) a = 0 :=
    (real_inner_comm _ _).trans (inner_self_euclideanCross a b)
  have hz₂ (a b : Space 3) : inner ℝ (euclideanCross a b) b = 0 :=
    (real_inner_comm _ _).trans (inner_euclideanCross_self a b)
  fin_cases i <;> fin_cases j <;> simp [tripleCofactors,h0,h1,h2,hz₁,hz₂]

noncomputable def tripleColumnLinear (u v w : Space 3) : Space 3 →ₗ[ℝ] Space 3 where
  toFun x := ∑ i : Fin 3, x i • (![u,v,w] i)
  map_add' x y := by simp only [PiLp.add_apply,add_smul,Finset.sum_add_distrib]
  map_smul' a x := by
    simp only [PiLp.smul_apply,smul_eq_mul,mul_smul,Finset.smul_sum,RingHom.id_apply]

noncomputable def tripleDualCoordinates (u v w x : Space 3) : Space 3 :=
  WithLp.toLp 2 (fun i => inner ℝ (tripleCofactors u v w i) x /
    inner ℝ u (euclideanCross v w))

theorem tripleDualCoordinates_column (u v w : Space 3)
    (ht : inner ℝ u (euclideanCross v w) ≠ 0) (x : Space 3) :
    tripleDualCoordinates u v w (tripleColumnLinear u v w x) = x := by
  apply PiLp.ext
  intro i
  change (inner ℝ (tripleCofactors u v w i)
    (∑ j : Fin 3, x j • (![u,v,w] j)))/inner ℝ u (euclideanCross v w) = x i
  simp only [inner_sum,inner_smul_right,tripleCofactors_inner]
  simp [mul_ite,ht]

theorem tripleColumnLinear_injective (u v w : Space 3)
    (ht : inner ℝ u (euclideanCross v w) ≠ 0) :
    Function.Injective (tripleColumnLinear u v w) :=
  Function.LeftInverse.injective (tripleDualCoordinates_column u v w ht)

noncomputable def tripleColumnEquiv (u v w : Space 3)
    (ht : inner ℝ u (euclideanCross v w) ≠ 0) : Space 3 ≃L[ℝ] Space 3 :=
  (LinearEquiv.ofBijective (tripleColumnLinear u v w)
    ⟨tripleColumnLinear_injective u v w ht,
      LinearMap.injective_iff_surjective.mp (tripleColumnLinear_injective u v w ht)⟩).toContinuousLinearEquiv

@[simp] theorem tripleColumnEquiv_apply (u v w : Space 3)
    (ht : inner ℝ u (euclideanCross v w) ≠ 0) (x : Space 3) :
    tripleColumnEquiv u v w ht x = tripleColumnLinear u v w x := rfl

theorem tripleColumnEquiv_symm_apply (u v w : Space 3)
    (ht : inner ℝ u (euclideanCross v w) ≠ 0) (x : Space 3) :
    (tripleColumnEquiv u v w ht).symm x = tripleDualCoordinates u v w x := by
  have hh := tripleDualCoordinates_column u v w ht ((tripleColumnEquiv u v w ht).symm x)
  rw [← tripleColumnEquiv_apply u v w ht,ContinuousLinearEquiv.apply_symm_apply] at hh
  exact hh.symm

end Falconer

end OAI
