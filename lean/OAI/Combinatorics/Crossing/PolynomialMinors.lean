import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Basic.Real.Basic

namespace OAI

noncomputable section
namespace Zarankiewicz
open Polynomial
open scoped BigOperators
variable {κ : Type*} [Fintype κ] [DecidableEq κ]

theorem natDegree_det_le_column_sum (M : Matrix κ κ ℝ[X]) (e : κ → ℕ)
    (he : ∀ i j, (M i j).natDegree ≤ e j) :
    M.det.natDegree ≤ ∑ j, e j := by
  rw [Matrix.det_apply]
  apply natDegree_sum_le_of_forall_le
  intro σ hσ
  apply (natDegree_smul_le _ _).trans
  exact (natDegree_prod_le _ _).trans (Finset.sum_le_sum fun j _ => he (σ j) j)

theorem pow_card_dvd_det_of_columns_vanish (M : Matrix κ κ ℝ[X]) (t : ℝ)
    (S : Finset κ) (hv : ∀ j ∈ S, ∀ i, (M i j).eval t = 0) :
    (X - C t)^S.card ∣ M.det := by
  let v : κ → ℝ[X] := fun j => if j ∈ S then X-C t else 1
  let A : Matrix κ κ ℝ[X] := fun i j => if j ∈ S then M i j /ₘ (X-C t) else M i j
  have hM : M = Matrix.of (fun i j => v j * A i j) := by
    funext i j
    by_cases hj : j ∈ S
    · simp only [Matrix.of_apply, v, A, hj, ite_true]
      exact (mul_divByMonic_eq_iff_isRoot.mpr (hv j hj i)).symm
    · simp [v, A, hj]
  have hprod : ∏ j, v j = (X-C t)^S.card := by
    simp [v]
  rw [hM, Matrix.det_mul_row, hprod]
  exact dvd_mul_right _ _

theorem prod_pow_roots_dvd {ι : Type*} [Fintype ι] (node : ι → ℝ)
    (hn : Function.Injective node) (q : ι → ℕ) (p : ℝ[X])
    (hq : ∀ i, (X-C (node i))^(q i) ∣ p) :
    (∏ i, (X-C (node i))^(q i)) ∣ p := by
  apply Fintype.prod_dvd_of_coprime _ hq
  intro i j hij
  exact (pairwise_coprime_X_sub_C hn hij).pow

theorem sum_multiplicities_le_natDegree {ι : Type*} [Fintype ι] (node : ι → ℝ)
    (hn : Function.Injective node) (q : ι → ℕ) (p : ℝ[X]) (hp : p ≠ 0)
    (hq : ∀ i, (X-C (node i))^(q i) ∣ p) :
    ∑ i, q i ≤ p.natDegree := by
  have hd := natDegree_le_of_dvd (prod_pow_roots_dvd node hn q p hq) hp
  rw [natDegree_prod_of_monic] at hd
  · simpa only [natDegree_pow, natDegree_X_sub_C, mul_one] using hd
  · intro i hi
    exact (monic_X_sub_C (node i)).pow (q i)

theorem sum_multiplicities_le_column_sum {ι : Type*} [Fintype ι]
    (node : ι → ℝ) (hn : Function.Injective node) (q : ι → ℕ)
    (M : Matrix κ κ ℝ[X]) (e : κ → ℕ) (hM : M.det ≠ 0)
    (he : ∀ i j, (M i j).natDegree ≤ e j)
    (hq : ∀ i, (X-C (node i))^(q i) ∣ M.det) :
    ∑ i, q i ≤ ∑ j, e j :=
  (sum_multiplicities_le_natDegree node hn q M.det hM hq).trans
    (natDegree_det_le_column_sum M e he)

end Zarankiewicz

end

end OAI
