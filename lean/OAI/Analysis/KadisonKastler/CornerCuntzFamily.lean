import OAI.Analysis.KadisonKastler.CuntzMatrices
import OAI.Analysis.KadisonKastler.InflatedConjugacy
import Mathlib.Logic.Equiv.Fin.Basic

namespace OAI

/-! # Common isometries from countable matrix units

Regrouping the countably many matrix summands gives the finite Cuntz
families used to identify matrix unit balls with ordinary unit balls.
The isometries belong to every von Neumann algebra containing the matrix
units, by their explicit strong-sum formula.
-/

namespace KadisonKastler

open Filter
open scoped BigOperators Topology

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {E : Submodule ℂ H} [CompleteSpace E]

namespace FullMatrixCorner

variable (F : FullMatrixCorner E)

theorem ext_on_columns {T U : H →L[ℂ] H}
    (h : ∀ k x, T (F.column k x) = U (F.column k x)) : T = U := by
  apply ContinuousLinearMap.ext
  intro x
  have he (s : Finset ℕ) : T (F.partialDiagonal s x) = U (F.partialDiagonal s x) := by
    simp only [partialDiagonal, sum_apply, map_sum]
    apply Finset.sum_congr rfl
    intro k _
    rw [F.diagonal_apply, h]
  exact tendsto_nhds_unique
    ((T.continuous.continuousAt.tendsto.comp (F.partialDiagonal_tendsto x)).congr he)
    (U.continuous.continuousAt.tendsto.comp (F.partialDiagonal_tendsto x))

theorem eq_of_inner_columns {x y : H}
    (h : ∀ k z, inner ℂ (F.column k z) x = inner ℂ (F.column k z) y) : x = y := by
  apply F.coordinates.injective
  apply lp.ext
  funext k
  apply ext_inner_left ℂ
  intro z
  have hx := F.coordinates.inner_map_map (F.column k z) x
  have hy := F.coordinates.inner_map_map (F.column k z) y
  rw [F.coordinates_column, lp.inner_single_left] at hx hy
  exact hx.trans ((h k z).trans hy.symm)

variable {n : Type*} (e : n × ℕ ≃ ℕ)

def regroupedColumns (i : n) (k : ℕ) : E →ₗᵢ[ℂ] H := F.column (e (i, k))

theorem regroupedColumns_orthogonal (i : n) :
    OrthogonalFamily ℂ (fun _ : ℕ => E) (F.regroupedColumns e i) := by
  intro k l hkl
  apply F.columns_orthogonal
  intro h
  exact hkl (congrArg Prod.snd (e.injective h))

/-- The isometry sending matrix summand `k` to summand `e (i,k)`. -/
def regroupingIsometry (i : n) : H →ₗᵢ[ℂ] H :=
  (F.regroupedColumns_orthogonal e i).linearIsometry.comp F.coordinates.toLinearIsometry

@[simp] theorem regroupingIsometry_column (i : n) (k : ℕ) (x : E) :
    F.regroupingIsometry e i (F.column k x) = F.column (e (i, k)) x := by
  change (F.regroupedColumns_orthogonal e i).linearIsometry
    (F.coordinates (F.column k x)) = _
  rw [F.coordinates_column, OrthogonalFamily.linearIsometry_apply_single]
  rfl

def regroupingOperator (i : n) : H →L[ℂ] H :=
  (F.regroupingIsometry e i).toContinuousLinearMap

@[simp] theorem regroupingOperator_column (i : n) (k : ℕ) (x : E) :
    F.regroupingOperator e i (F.column k x) = F.column (e (i, k)) x :=
  F.regroupingIsometry_column e i k x

variable [DecidableEq n]

theorem adjoint_regrouping_column (i j : n) (k : ℕ) (x : E) :
    star (F.regroupingOperator e i) (F.column (e (j, k)) x) =
      if i = j then F.column k x else 0 := by
  apply F.eq_of_inner_columns
  intro l y
  rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right,
    F.regroupingOperator_column]
  simp only [column_apply]
  rw [F.inner_columns]
  by_cases hij : i = j
  · subst j
    by_cases hlk : l = k
    · subst k
      simp [F.inner_columns]
    · have hh : e (i, l) ≠ e (i, k) := fun h => hlk (congrArg Prod.snd (e.injective h))
      simp [hh, F.inner_columns, hlk]
  · have hh : e (i, l) ≠ e (j, k) := fun h => hij (congrArg Prod.fst (e.injective h))
    simp [hh, hij]

theorem regrouping_orthogonal (i j : n) :
    star (F.regroupingOperator e i) * F.regroupingOperator e j =
      if i = j then 1 else 0 := by
  apply F.ext_on_columns
  intro k x
  simp only [mul_apply_eq_comp, F.regroupingOperator_column, F.adjoint_regrouping_column]
  split_ifs <;> rfl

variable [Fintype n]

theorem regrouping_total :
    ∑ i, F.regroupingOperator e i * star (F.regroupingOperator e i) = 1 := by
  apply F.ext_on_columns
  intro k x
  obtain ⟨⟨j, l⟩, rfl⟩ := e.surjective k
  simp only [sum_apply, mul_apply_eq_comp, F.adjoint_regrouping_column]
  simp only [apply_ite, map_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  exact F.regroupingOperator_column e j l x

/-- This construction is independent of the algebra that contains the
matrix units, so the same family can be used on both sides of a gap. -/
def cuntzFamily : CuntzFamily n H where
  entry := F.regroupingOperator e
  orthogonal := F.regrouping_orthogonal e
  total := F.regrouping_total e

omit [Fintype n] [DecidableEq n] in
theorem regroupingOperator_mem (M : VonNeumannAlgebra H)
    (hM : ∀ i j, F.entry i j ∈ M) (i : n) : F.regroupingOperator e i ∈ M := by
  let a (s : Finset ℕ) : Algebra M :=
    ⟨∑ k ∈ s, F.entry (e (i, k)) k, M.sum_mem fun k _ => hM _ _⟩
  apply Generator.Tracial.weak_operator_limit_mem (l := atTop) M a
  intro x y
  have he (s : Finset ℕ) :
      (a s : H →L[ℂ] H) x = F.regroupingOperator e i (F.partialDiagonal s x) := by
    simp only [a, partialDiagonal, sum_apply, map_sum]
    apply Finset.sum_congr rfl
    intro k _
    rw [F.diagonal_apply, F.regroupingOperator_column]
    change F.entry (e (i, k)) k x =
      (F.entry (e (i, k)) 0 * E.starProjection * F.entry 0 k) x
    rw [← F.zero_zero, F.mul_entry, ite_eq_left rfl, F.mul_entry, ite_eq_left rfl]
  exact (tendsto_const_nhds.inner (𝕜 := ℂ)
    ((F.regroupingOperator e i).continuous.continuousAt.tendsto.comp
      (F.partialDiagonal_tendsto x))).congr
    (fun s => congrArg (inner ℂ y) (he s).symm)

theorem cuntzFamily_mem (M : VonNeumannAlgebra H)
    (hM : ∀ i j, F.entry i j ∈ M) (i : n) : (F.cuntzFamily e).entry i ∈ M :=
  F.regroupingOperator_mem e M hM i

/-- Every positive matrix size is obtained from the same countable matrix
units by the quotient-and-remainder bijection. -/
def finiteCuntz (n : ℕ) [NeZero n] : CuntzFamily (Fin n) H :=
  F.cuntzFamily ((Equiv.prodComm (Fin n) ℕ).trans (Nat.divModEquiv n).symm)

theorem finiteCuntz_mem (n : ℕ) [NeZero n] (M : VonNeumannAlgebra H)
    (hM : ∀ i j, F.entry i j ∈ M) (i : Fin n) : (F.finiteCuntz n).entry i ∈ M :=
  F.cuntzFamily_mem _ M hM i

/-- There is no growth in the perturbation tolerance at any positive
matrix size when both algebras contain these countable matrix units. -/
theorem matrix_hausdorffDist_eq (n : ℕ) [NeZero n] (M N : VonNeumannAlgebra H)
    (hM : ∀ i j, F.entry i j ∈ M) (hN : ∀ i j, F.entry i j ∈ N) :
    Metric.hausdorffDist (CuntzFamily.matrixUnitBall (n := Fin n) M)
      (CuntzFamily.matrixUnitBall (n := Fin n) N) = kkDistance M N :=
  (F.finiteCuntz n).matrix_hausdorffDist_eq M N
    (F.finiteCuntz_mem n M hM) (F.finiteCuntz_mem n N hN)

end FullMatrixCorner

end

end KadisonKastler

end OAI
