import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.Matrix.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finiteness
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Tactic.Ring
import OAI.Computability.UniqueGames.Inverse.AffineWitnessLemmas
import OAI.Computability.UniqueGames.Inverse.AffineWitnessNormalizationLemmas
import OAI.Computability.UniqueGames.Inverse.MatrixChartIntervalsLemmas
import OAI.Computability.UniqueGames.Inverse.MatrixChartLemmas

namespace OAI

section

/-!
The shortcode inverse principle uses an arbitrary table function, full uniform
factor sampling, and an affine intercept.
-/

namespace UniqueGamesTheorem.Inverse.Shortcode

noncomputable section
open scoped BigOperators Classical

abbrev F2 := ZMod 2
abbrev Vector (n : ℕ) := Fin n → F2
abbrev Mat (ell m : ℕ) := Matrix (Fin ell) (Fin m) F2

def rankOne {ell m : ℕ} (a : Vector ell) (l : Vector m) : Mat ell m :=
  fun i j => a i * l j

def evaluate {ell m : ℕ} (M : Mat ell m) (z : Vector m) : Vector ell :=
  fun i => ∑ j, M i j * z j

@[simp] theorem evaluate_zero {ell m : ℕ} (M : Mat ell m) : evaluate M 0 = 0 := by
  ext i
  simp [evaluate]

@[simp] theorem rankOne_zero_left {ell m : ℕ} (l : Vector m) :
    rankOne (0 : Vector ell) l = 0 := by
  ext i j
  simp [rankOne]

@[simp] theorem rankOne_zero_right {ell m : ℕ} (a : Vector ell) :
    rankOne a (0 : Vector m) = 0 := by
  ext i j
  simp [rankOne]

/-- Both perturbation factors are independent uniform vectors, including zero.
The matrix is sampled independently as well. -/
def equalityAcceptance {ell m : ℕ} (f : Mat ell m → Vector ell) : ℝ :=
  𝔼 M, 𝔼 a, 𝔼 l, if f M = f (M + rankOne a l) then 1 else 0

/-- A description includes possibly dependent equations; the row and column
counts need not equal their ranks. -/
structure Slice (ell m : ℕ) where
  rows : ℕ
  columns : ℕ
  rowCoefficient : Fin rows → Vector ell
  rowValue : Fin rows → Vector m
  columnCoefficient : Fin columns → Vector m
  columnValue : Fin columns → Vector ell

def Slice.Contains {ell m : ℕ} (S : Slice ell m) (M : Mat ell m) : Prop :=
  (∀ i j, (∑ a, S.rowCoefficient i a * M a j) = S.rowValue i j) ∧
    ∀ i, evaluate M (S.columnCoefficient i) = S.columnValue i

def Slice.points {ell m : ℕ} (S : Slice ell m) : Finset (Mat ell m) :=
  Finset.univ.filter S.Contains

def Slice.affineAgreement {ell m : ℕ} (S : Slice ell m)
    (f : Mat ell m → Vector ell) (z : Vector m) (u : Vector ell) : ℝ :=
  S.points.expect fun M => if f M = evaluate M z + u then 1 else 0

def Slice.constantAgreement {ell m : ℕ} (S : Slice ell m)
    (f : Mat ell m → Vector ell) (u : Vector ell) : ℝ :=
  S.points.expect fun M => if f M = u then 1 else 0

/-- The fiber/Grassmann route produces the constant affine target `0,u`.
Keeping `u` is essential: this result does not claim a homogeneous target. -/
theorem Slice.constantAgreement_eq_affine {ell m : ℕ} (S : Slice ell m)
    (f : Mat ell m → Vector ell) (u : Vector ell) :
    S.constantAgreement f u = S.affineAgreement f 0 u := by
  simp [Slice.constantAgreement, Slice.affineAgreement]

def HasAffineSlice {ell m : ℕ} (f : Mat ell m → Vector ell) (α : ℝ) (r : ℕ) : Prop :=
  ∃ S : Slice ell m, S.rows ≤ r ∧ S.columns ≤ r ∧ S.points.Nonempty ∧
    ∃ z : Vector m, ∃ u : Vector ell, α ≤ S.affineAgreement f z u

theorem hasAffineSlice_of_constant {ell m : ℕ} (f : Mat ell m → Vector ell)
    (α : ℝ) (r : ℕ) (S : Slice ell m) (hrows : S.rows ≤ r)
    (hcolumns : S.columns ≤ r) (hne : S.points.Nonempty) (u : Vector ell)
    (h : α ≤ S.constantAgreement f u) : HasAffineSlice f α r := by
  exact ⟨S, hrows, hcolumns, hne, 0, u, by
    simpa only [S.constantAgreement_eq_affine f u] using h⟩

/-- Dimension-uniform inverse statement. The constants `α,r` depend only
on `η`; only the final input dimension threshold may depend on `ell`. There is
no folding assumption, and no inverse-theorem certificate is hidden in `f`. -/
def InversePrinciple : Prop :=
  ∀ η : ℝ, 0 < η → η < 1 →
    ∃ α : ℝ, 0 < α ∧ α ≤ 1 ∧ ∃ r : ℕ, 1 ≤ r ∧
      ∃ ell₀ : ℕ, ∀ ell : ℕ, ell₀ ≤ ell →
        ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m →
          ∀ f : Mat ell m → Vector ell,
            η ≤ equalityAcceptance f → HasAffineSlice f α r

end
end UniqueGamesTheorem.Inverse.Shortcode

end

section

/-!
The exact sampling bridge from the vector factors in the shortcode test
to actual KMS Grassmann vertices. Every nonzero vector pair is sent to the
matrix `M + rankOne a l`, and this is a bijection onto the chart neighbors.
-/

namespace UniqueGamesTheorem.Inverse.MatrixChart

open Matrix
open Shortcode (Vector Mat rankOne)

variable {ell m : ℕ}

@[simp] theorem dotFunctional_zero_binary :
    dotFunctional (0 : Vector ell) = 0 := by
  apply LinearMap.ext
  intro x
  change (0 : Vector ell) ⬝ᵥ x = 0
  simp

theorem dotFunctional_ne_zero {a : Vector ell} (ha : a ≠ 0) :
    dotFunctional a ≠ 0 := by
  intro h
  exact ha (dotFunctional_injective (h.trans dotFunctional_zero_binary.symm))

/-- The shortcode outer product is precisely the rank-one chart map. -/
theorem vecMulLinear_rankOne (a : Vector ell) (l : Vector m) :
    (rankOne a l).vecMulLinear = (dotFunctional a).smulRight l := by
  apply LinearMap.ext
  intro x
  change x ᵥ* Matrix.vecMulVec a l = (a ⬝ᵥ x) • l
  rw [Matrix.vecMul_vecMulVec, dotProduct_comm x a]

/-- This is the exact perturbation, including its functional/vector order. -/
theorem vecMulLinear_add_rankOne (M : Mat ell m) (a : Vector ell) (l : Vector m) :
    (M + rankOne a l).vecMulLinear = M.vecMulLinear + (dotFunctional a).smulRight l := by
  apply LinearMap.ext
  intro x
  change x ᵥ* (M + rankOne a l) = M.vecMulLinear x +
    ((dotFunctional a).smulRight l) x
  rw [Matrix.vecMul_add]
  exact congrArg (fun y => M.vecMulLinear x + y)
    (LinearMap.congr_fun (vecMulLinear_rankOne a l) x)

theorem adjacent_matrixVertex_add_rankOne (M : Mat ell m)
    (a : Vector ell) (l : Vector m) (ha : a ≠ 0) (hl : l ≠ 0) :
    KMS.Adjacent (matrixVertex M) (matrixVertex (M + rankOne a l)) := by
  apply (adjacent_matrixVertex_iff M (M + rankOne a l)).mpr
  apply (adjacent_iff_rank_one M.vecMulLinear (M + rankOne a l).vecMulLinear).mp
  rw [vecMulLinear_add_rankOne]
  exact adjacent_rank_one_step M.vecMulLinear (dotFunctional a) l
    (dotFunctional_ne_zero ha) hl

abbrev NonzeroVectorFactors (ell m : ℕ) :=
  {a : Vector ell // a ≠ 0} × {l : Vector m // l ≠ 0}

/-- Actual Grassmann vertices adjacent to `matrixVertex M` and remaining
inside the finite matrix chart. -/
abbrev MatrixVertexChartNeighbors (M : Mat ell m) :=
  {L : KMS.Vertex (ell + m) ell //
    KMS.Adjacent (matrixVertex M) L ∧ L ∈ matrixChart ell m}

def vectorFactorMatrixNeighbor (M : Mat ell m) (p : NonzeroVectorFactors ell m) :
    MatrixVertexChartNeighbors M :=
  ⟨matrixVertex (M + rankOne p.1.val p.2.val),
    adjacent_matrixVertex_add_rankOne M p.1.val p.2.val p.1.property p.2.property,
    (mem_matrixChart _).mpr ⟨M + rankOne p.1.val p.2.val, rfl⟩⟩

theorem vectorFactorMatrixNeighbor_injective (M : Mat ell m) :
    Function.Injective (vectorFactorMatrixNeighbor M) := by
  intro p q h
  have hM : M + rankOne p.1.val p.2.val = M + rankOne q.1.val q.2.val :=
    matrixVertex_injective (congrArg Subtype.val h)
  have hrank := congrArg Matrix.vecMulLinear (add_left_cancel hM)
  rw [vecMulLinear_rankOne, vecMulLinear_rankOne] at hrank
  obtain ⟨ha, hl⟩ := binary_smulRight_unique (dotFunctional_ne_zero p.1.property)
    p.2.property hrank
  exact Prod.ext (Subtype.ext (dotFunctional_injective ha)) (Subtype.ext hl)

theorem vectorFactorMatrixNeighbor_surjective (M : Mat ell m) :
    Function.Surjective (vectorFactorMatrixNeighbor M) := by
  intro L
  obtain ⟨N, hN⟩ := (mem_matrixChart L.val).mp L.property.2
  have hMN : KMS.Adjacent (matrixVertex M) (matrixVertex N) := by
    rw [hN]
    exact L.property.1
  have hNM : KMS.Adjacent (matrixVertex N) (matrixVertex M) :=
    ⟨hMN.1.symm, by rw [inf_comm]; exact hMN.2⟩
  obtain ⟨a, l, ha, hl, hfactor⟩ := exists_smulRight_of_rank_one
    (N.vecMulLinear - M.vecMulLinear) ((adjacent_matrixVertex_iff N M).mp hNM)
  obtain ⟨v, hv⟩ := dotFunctional_surjective a
  have hv0 : v ≠ 0 := by
    intro h
    apply ha
    rw [← hv, h, dotFunctional_zero_binary]
  have hmatrix : M + rankOne v l = N := by
    apply (LinearMap.toMatrixRight' (R := ZMod 2)).symm.injective
    change (M + rankOne v l).vecMulLinear = N.vecMulLinear
    rw [vecMulLinear_add_rankOne, hv]
    simpa only [add_comm] using (sub_eq_iff_eq_add.mp hfactor).symm
  refine ⟨(⟨v, hv0⟩, ⟨l, hl⟩), ?_⟩
  apply Subtype.ext
  change matrixVertex (M + rankOne v l) = L.val
  rw [hmatrix]
  exact hN

/-- Uniform independent nonzero vector factors induce exactly uniform
neighbors of the actual Grassmann vertex within the matrix chart. -/
noncomputable def vectorFactorsEquivMatrixVertexChartNeighbors (M : Mat ell m) :
    NonzeroVectorFactors ell m ≃ MatrixVertexChartNeighbors M :=
  Equiv.ofBijective (vectorFactorMatrixNeighbor M)
    ⟨vectorFactorMatrixNeighbor_injective M, vectorFactorMatrixNeighbor_surjective M⟩

@[simp] theorem vectorFactorsEquivMatrixVertexChartNeighbors_apply (M : Mat ell m)
    (p : NonzeroVectorFactors ell m) :
    (vectorFactorsEquivMatrixVertexChartNeighbors M p).val =
      matrixVertex (M + rankOne p.1.val p.2.val) := rfl

/-- The chart degree in the actual KMS vertex type. -/
theorem card_matrixVertexChartNeighbors (M : Mat ell m) :
    Nat.card (MatrixVertexChartNeighbors M) = (2 ^ ell - 1) * (2 ^ m - 1) := by
  classical
  rw [← Nat.card_congr (vectorFactorsEquivMatrixVertexChartNeighbors M)]
  simp only [NonzeroVectorFactors, Nat.card_eq_fintype_card, Fintype.card_prod,
    Fintype.card_subtype_compl, Fintype.card_subtype_eq,
    Shortcode.Vector, Fintype.card_fun, ZMod.card, Fintype.card_fin]

end UniqueGamesTheorem.Inverse.MatrixChart

end

section

/-! The concrete interface consumed by the shortcode assembly: an arbitrary
KMS interval becomes a `Shortcode.Slice`, with exact equation counts.
-/

namespace UniqueGamesTheorem.Inverse.MatrixChart

open Matrix

theorem exists_shortcode_slice {ell m : Nat}
    (A B : Submodule (ZMod 2) (KMS.Ambient (ell + m))) :
    ∃ S : Shortcode.Slice ell m,
      S.rows = Module.finrank (ZMod 2) A ∧
      S.columns = (ell + m) - Module.finrank (ZMod 2) B ∧
      ∀ M : Shortcode.Mat ell m,
        S.Contains M ↔ A ≤ (matrixVertex M).val ∧ (matrixVertex M).val ≤ B := by
  classical
  let e := coordinateJoin (ZMod 2) ell m
  let A' := A.comap e.toLinearMap
  let B' := B.comap e.toLinearMap
  have hA : Module.finrank (ZMod 2) A' = Module.finrank (ZMod 2) A := by
    rw [show A' = A.map e.symm.toLinearMap from
      Submodule.comap_equiv_eq_map_symm e A]
    exact e.symm.finrank_map_eq A
  have hB : Module.finrank (ZMod 2) B' = Module.finrank (ZMod 2) B := by
    rw [show B' = B.map e.symm.toLinearMap from
      Submodule.comap_equiv_eq_map_symm e B]
    exact e.symm.finrank_map_eq B
  obtain ⟨nr, nc, d, s, t, q, hnr, hnc, h⟩ := exists_matrix_interval_slice A' B'
  have hE : Module.finrank (ZMod 2)
      ((Fin ell → ZMod 2) × (Fin m → ZMod 2)) = ell + m := by simp
  have hnc' : nc = (ell + m) - Module.finrank (ZMod 2) B := by
    simpa only [Submodule.finrank_quotient, hE, hB] using hnc
  let S : Shortcode.Slice ell m := ⟨nr, nc, d, s, q, t⟩
  refine ⟨S, hnr.trans hA, hnc', ?_⟩
  intro M
  have hcontains : S.Contains M ↔
      (∀ i, d i ᵥ* M = s i) ∧ (∀ j, M *ᵥ q j = t j) := by
    constructor
    · rintro ⟨hr, hc⟩
      exact ⟨fun i => funext (hr i), hc⟩
    · rintro ⟨hr, hc⟩
      exact ⟨fun i j => congrFun (hr i) j, hc⟩
  rw [hcontains, ← h M]
  have hlow : A' ≤ matrixGraph M ↔ A ≤ (matrixVertex M).val := by
    change A.comap e.toLinearMap ≤ matrixGraph M ↔
      A ≤ (matrixGraph M).map e.toLinearMap
    have hh := Submodule.comap_le_comap_iff_of_surjective
      (f := e.toLinearMap) e.surjective (p := A)
      (q := (matrixGraph M).map e.toLinearMap)
    simpa only [Submodule.comap_map_eq_of_injective e.injective] using hh
  have hupp : matrixGraph M ≤ B' ↔ (matrixVertex M).val ≤ B :=
    Submodule.map_le_iff_le_comap.symm
  exact and_congr hlow hupp

end UniqueGamesTheorem.Inverse.MatrixChart

end

section

/-!
The size bound for simultaneous row/column slices.
Starting at any point of a nonempty slice, maps from the quotient by its column
span into the common row kernel give distinct points of that same affine slice.
Rank-nullity gives the dimension lower bound even when equations are dependent.
This argument uses only finite-dimensional linear algebra.
-/

namespace UniqueGamesTheorem.Inverse.Shortcode

noncomputable section
open scoped BigOperators Matrix

namespace Slice

variable {ell m : ℕ}

/-- The simultaneous row functionals, allowing dependent and zero rows. -/
def rowMap (S : Slice ell m) : Vector ell →ₗ[F2] Vector S.rows :=
  Matrix.mulVecLin S.rowCoefficient

/-- Column specifications fix the matrix on this entire subspace. -/
def columnSpan (S : Slice ell m) : Submodule F2 (Vector m) :=
  Submodule.span F2 (Set.range S.columnCoefficient)

/-- Free directions of a row/column slice, intrinsically as quotient maps. -/
abbrev Directions (S : Slice ell m) :=
  (Vector m ⧸ S.columnSpan) →ₗ[F2] S.rowMap.ker

def directionMap (S : Slice ell m) (N : S.Directions) :
    Vector m →ₗ[F2] Vector ell :=
  S.rowMap.ker.subtype.comp (N.comp S.columnSpan.mkQ)

def directionMatrix (S : Slice ell m) (N : S.Directions) : Mat ell m :=
  LinearMap.toMatrix' (S.directionMap N)

theorem directionMatrix_injective (S : Slice ell m) :
    Function.Injective S.directionMatrix := by
  intro N P h
  have hmap : S.directionMap N = S.directionMap P :=
    LinearMap.toMatrix'.injective h
  apply LinearMap.ext
  intro x
  obtain ⟨v, rfl⟩ := S.columnSpan.mkQ_surjective x
  apply Subtype.ext
  exact congrArg (fun f : Vector m →ₗ[F2] Vector ell => f v) hmap

theorem directionMatrix_row (S : Slice ell m) (N : S.Directions)
    (i : Fin S.rows) (j : Fin m) :
    (∑ a, S.rowCoefficient i a * S.directionMatrix N a j) = 0 := by
  have h := (N (S.columnSpan.mkQ (Pi.single j 1))).property
  have hi := congrFun h i
  change (∑ a, S.rowCoefficient i a *
    (N (S.columnSpan.mkQ (Pi.single j 1)) : Vector ell) a) = 0 at hi
  exact hi

theorem directionMatrix_column (S : Slice ell m) (N : S.Directions)
    (i : Fin S.columns) :
    evaluate (S.directionMatrix N) (S.columnCoefficient i) = 0 := by
  have hq : S.columnSpan.mkQ (S.columnCoefficient i) = 0 := by
    apply (Submodule.Quotient.mk_eq_zero S.columnSpan).mpr
    exact Submodule.subset_span ⟨i, rfl⟩
  change (S.directionMatrix N) *ᵥ (S.columnCoefficient i) = 0
  rw [directionMatrix, LinearMap.toMatrix'_mulVec]
  simp [directionMap, hq]

theorem contains_add_direction (S : Slice ell m) (M : Mat ell m)
    (hM : S.Contains M) (N : S.Directions) :
    S.Contains (M + S.directionMatrix N) := by
  constructor
  · intro i j
    simp only [Matrix.add_apply, mul_add, Finset.sum_add_distrib]
    rw [hM.1 i j, S.directionMatrix_row N i j, add_zero]
  · intro i
    have hd := S.directionMatrix_column N i
    change evaluate (M + S.directionMatrix N) (S.columnCoefficient i) = _
    have he : evaluate (M + S.directionMatrix N) (S.columnCoefficient i) =
        evaluate M (S.columnCoefficient i) +
          evaluate (S.directionMatrix N) (S.columnCoefficient i) := by
      ext a
      simp [evaluate, add_mul, Finset.sum_add_distrib]
    rw [he, hM.2 i, hd, add_zero]

def directionEmbedding (S : Slice ell m) (M : Mat ell m) (hM : S.Contains M) :
    S.Directions ↪ S.points where
  toFun N := ⟨M + S.directionMatrix N, by
    simp only [points, Finset.mem_filter, Finset.mem_univ, true_and]
    exact S.contains_add_direction M hM N⟩
  inj' := by
    intro N P h
    apply S.directionMatrix_injective
    exact add_left_cancel (congrArg Subtype.val h)

theorem columnSpan_finrank_le (S : Slice ell m) :
    Module.finrank F2 S.columnSpan ≤ S.columns := by
  have h := finrank_range_le_card (R := F2) (M := Vector m) S.columnCoefficient
  change Module.finrank F2 (Submodule.span F2 (Set.range S.columnCoefficient)) ≤
    Fintype.card (Fin S.columns) at h
  rw [Fintype.card_fin] at h
  exact h

theorem quotient_finrank_ge (S : Slice ell m) :
    m - S.columns ≤ Module.finrank F2 (Vector m ⧸ S.columnSpan) := by
  have h := S.columnSpan.finrank_quotient_add_finrank
  have hspan := S.columnSpan_finrank_le
  have hm : Module.finrank F2 (Vector m) = m := by simp [Vector]
  rw [hm] at h
  omega

theorem rowKernel_finrank_ge (S : Slice ell m) :
    ell - S.rows ≤ Module.finrank F2 S.rowMap.ker := by
  have h := S.rowMap.finrank_range_add_finrank_ker
  have hrange : Module.finrank F2 S.rowMap.range ≤ S.rows := by
    exact S.rowMap.range.finrank_le.trans_eq (by simp [Vector])
  have hell : Module.finrank F2 (Vector ell) = ell := by simp [Vector]
  rw [hell] at h
  omega

theorem card_directions (S : Slice ell m) :
    Nat.card S.Directions =
      2 ^ (Module.finrank F2 (Vector m ⧸ S.columnSpan) *
        Module.finrank F2 S.rowMap.ker) := by
  rw [Module.natCard_eq_pow_finrank (K := F2), Module.finrank_linearMap]
  simp [F2]

/-- A nonempty affine slice is at least as large as its free-direction space. -/
theorem card_directions_le (S : Slice ell m) (hne : S.points.Nonempty) :
    Nat.card S.Directions ≤ S.points.card := by
  obtain ⟨M, hM⟩ := hne
  have hcontains : S.Contains M := by simpa only [points, Finset.mem_filter,
    Finset.mem_univ, true_and] using hM
  simpa only [Nat.card_eq_finsetCard] using
    Nat.card_le_card_of_injective (S.directionEmbedding M hcontains)
      (S.directionEmbedding M hcontains).injective

/-- The size bound, with truncation making it valid also in small dimensions.
There is no independence hypothesis on the listed equations. -/
theorem pow_dimension_le_card (S : Slice ell m) (r : ℕ)
    (hrows : S.rows ≤ r) (hcolumns : S.columns ≤ r)
    (hne : S.points.Nonempty) :
    2 ^ ((ell - r) * (m - r)) ≤ S.points.card := by
  have hrow : ell - r ≤ Module.finrank F2 S.rowMap.ker :=
    (Nat.sub_le_sub_left hrows ell).trans S.rowKernel_finrank_ge
  have hcol : m - r ≤ Module.finrank F2 (Vector m ⧸ S.columnSpan) :=
    (Nat.sub_le_sub_left hcolumns m).trans S.quotient_finrank_ge
  have hmul := Nat.mul_le_mul hcol hrow
  rw [Nat.mul_comm (m - r) (ell - r)] at hmul
  have hp := Nat.pow_le_pow_right (by decide : 1 ≤ 2) hmul
  rw [← S.card_directions] at hp
  exact hp.trans (S.card_directions_le hne)

end Slice
end
end UniqueGamesTheorem.Inverse.Shortcode

end

section

/-! Exact connection between the finite-array shortcode slices and the
linear-map slices used by affine witness normalization. -/

namespace UniqueGamesTheorem.Inverse.Shortcode

noncomputable section
open scoped BigOperators Classical Matrix

namespace Slice

variable {ell m : ℕ}

theorem evaluate_eq_toLin (M : Mat ell m) (z : Vector m) :
    evaluate M z = Matrix.toLin' M z := rfl

theorem row_equations_iff (S : Slice ell m) (M : Mat ell m) :
    (∀ i j, (∑ a, S.rowCoefficient i a * M a j) = S.rowValue i j) ↔
      S.rowMap.comp (Matrix.toLin' M) = Matrix.toLin' S.rowValue := by
  let A : Matrix (Fin S.rows) (Fin ell) F2 := S.rowCoefficient
  let B : Matrix (Fin S.rows) (Fin m) F2 := S.rowValue
  change (∀ i j, (∑ a, A i a * M a j) = B i j) ↔
    (Matrix.toLin' A).comp (Matrix.toLin' M) = Matrix.toLin' B
  constructor
  · intro h
    have hm : A * M = B := by
      ext i j
      exact h i j
    rw [← Matrix.toLin'_mul, hm]
  · intro h
    have hm : A * M = B := by
      apply Matrix.toLin'.injective
      rw [Matrix.toLin'_mul]
      exact h
    intro i j
    exact congrFun (congrFun hm i) j

/-- This is an equivalence of the actual equations, not merely a cardinality
comparison or a homogeneous approximation of the affine slice. -/
theorem contains_iff_inSlice (S : Slice ell m) (M₀ : Mat ell m)
    (hM₀ : S.Contains M₀) (M : Mat ell m) :
    S.Contains M ↔
      AffineWitness.InSlice S.rowMap S.columnSpan
        (Matrix.toLin' M₀) (Matrix.toLin' M) := by
  have hrow₀ := (S.row_equations_iff M₀).mp hM₀.1
  have hcol₀ : ∀ i, Matrix.toLin' M₀ (S.columnCoefficient i) =
      S.columnValue i := hM₀.2
  have heq := AffineWitness.explicit_slice_iff S.rowMap
    (Matrix.toLin' S.rowValue) S.columnCoefficient S.columnValue
    (Matrix.toLin' M₀) (Matrix.toLin' M) hrow₀ hcol₀
  constructor
  · intro hM
    exact heq.mp ⟨(S.row_equations_iff M).mp hM.1, hM.2⟩
  · intro hM
    have h := heq.mpr hM
    exact ⟨(S.row_equations_iff M).mpr h.1, h.2⟩

/-- Exact finite sample-space equivalence between the matrix representation
and the linear-map representation of a nonempty affine slice. -/
def linearSliceEquiv (S : Slice ell m) (M₀ : Mat ell m)
    (hM₀ : S.Contains M₀) :
    S.points ≃ AffineWitness.Slice S.rowMap S.columnSpan (Matrix.toLin' M₀) where
  toFun M := ⟨Matrix.toLin' M.val,
    (S.contains_iff_inSlice M₀ hM₀ M.val).mp (by
      simpa only [points, Finset.mem_filter, Finset.mem_univ, true_and] using M.property)⟩
  invFun N := ⟨LinearMap.toMatrix' N.val, by
    simp only [points, Finset.mem_filter, Finset.mem_univ, true_and]
    apply (S.contains_iff_inSlice M₀ hM₀ _).mpr
    simpa only [Matrix.toLin'_toMatrix'] using N.property⟩
  left_inv M := by
    apply Subtype.ext
    exact LinearMap.toMatrix'_toLin' M.val
  right_inv N := by
    apply Subtype.ext
    exact Matrix.toLin'_toMatrix' N.val

/-- Pointwise preservation on the genuine slice preserves its exact uniform
affine agreement, including the empty-slice convention. -/
theorem affineAgreement_eq_of_target_eq (S : Slice ell m)
    (f : Mat ell m → Vector ell) (z z' : Vector m) (u u' : Vector ell)
    (htarget : ∀ M, S.Contains M → evaluate M z' + u' = evaluate M z + u) :
    S.affineAgreement f z' u' = S.affineAgreement f z u := by
  unfold affineAgreement
  apply Finset.expect_congr rfl
  intro M hM
  have hcontains : S.Contains M := by
    simpa only [points, Finset.mem_filter, Finset.mem_univ, true_and] using hM
  rw [htarget M hcontains]

theorem affineAgreement_eq_of_linear_target_eq (S : Slice ell m)
    (M₀ : Mat ell m) (hM₀ : S.Contains M₀)
    (f : Mat ell m → Vector ell) (z z' : Vector m) (u u' : Vector ell)
    (htarget : ∀ M, AffineWitness.InSlice S.rowMap S.columnSpan
      (Matrix.toLin' M₀) M → M z' + u' = M z + u) :
    S.affineAgreement f z' u' = S.affineAgreement f z u := by
  apply S.affineAgreement_eq_of_target_eq f z z' u u'
  intro M hM
  exact htarget (Matrix.toLin' M) ((S.contains_iff_inSlice M₀ hM₀ M).mp hM)

/-- Changing the representative inside the column span and correcting the
intercept leaves the shortcode agreement exactly unchanged. -/
theorem affineAgreement_translate (S : Slice ell m)
    (M₀ : Mat ell m) (hM₀ : S.Contains M₀)
    (f : Mat ell m → Vector ell) (z w : Vector m) (hw : w ∈ S.columnSpan)
    (u : Vector ell) :
    S.affineAgreement f (z + w) (u + evaluate M₀ w) =
      S.affineAgreement f z u := by
  apply S.affineAgreement_eq_of_linear_target_eq M₀ hM₀ f z (z + w) u _
  intro M hM
  exact AffineWitness.translate_target S.rowMap S.columnSpan (Matrix.toLin' M₀)
    M hM z w hw u

end Slice
end
end UniqueGamesTheorem.Inverse.Shortcode

end

section

/-! First-bit normalization in the actual finite-array shortcode API. The
sample space, event count, affine intercept, and folding law are transported
exactly; no inverse result is assumed by the representation bridge. -/

namespace UniqueGamesTheorem.Inverse.Shortcode

noncomputable section
open scoped BigOperators Classical

variable {ell m : ℕ}

/-- The coordinate row of a binary linear functional. -/
def functionalRow (e : Vector m →ₗ[F2] F2) : Vector m :=
  fun j => e (Pi.single j 1)

theorem toMatrix_shift (e : Vector m →ₗ[F2] F2) (h : Vector ell)
    (M : Mat ell m) :
    LinearMap.toMatrix' (AffineWitness.shift e h (Matrix.toLin' M)) =
      M + rankOne h (functionalRow e) := by
  rw [AffineWitness.shift, map_add, LinearMap.toMatrix'_toLin']
  congr 1
  ext i j
  simp only [LinearMap.toMatrix'_apply, LinearMap.smulRight_apply,
    Pi.smul_apply, smul_eq_mul, rankOne, functionalRow, mul_comm]

namespace Slice

/-- Exact density identity on the complete nonempty affine slice, with no
lost conditioning factor in the change from matrices to linear maps. -/
theorem affineAgreement_eq_linear_ratio (S : Slice ell m)
    (M₀ : Mat ell m) (hM₀ : S.Contains M₀)
    (f : Mat ell m → Vector ell) (z : Vector m) (u : Vector ell) :
    S.affineAgreement f z u =
      (Nat.card {N : AffineWitness.Slice S.rowMap S.columnSpan (Matrix.toLin' M₀) //
        f (LinearMap.toMatrix' N.val) = N.val z + u} : ℝ) /
      (Nat.card (AffineWitness.Slice S.rowMap S.columnSpan (Matrix.toLin' M₀)) : ℝ) := by
  unfold affineAgreement
  apply finset_expect_indicator_eq_card_ratio_of_equiv S.points
    (fun M => f M = evaluate M z + u) (S.linearSliceEquiv M₀ hM₀)
    (fun N => f (LinearMap.toMatrix' N.val) = N.val z + u)
  intro M
  change (f M.val = evaluate M.val z + u) ↔
    (f (LinearMap.toMatrix' (Matrix.toLin' M.val)) = Matrix.toLin' M.val z + u)
  rw [LinearMap.toMatrix'_toLin']
  rfl

/-- First-bit normalization for the exact selected shortcode slice.
The original affine agreement is preserved, not merely bounded below. -/
theorem first_bit_normalization (S : Slice ell m)
    (M₀ : Mat ell m) (hM₀ : S.Contains M₀)
    (e : Vector m →ₗ[F2] F2)
    (f : Mat ell m → Vector ell) (z : Vector m) (u : Vector ell)
    (hfold : ∀ (h : S.rowMap.ker) M,
      f (M + rankOne h (functionalRow e)) = f M + h)
    (α : ℝ) (hα : 0 < α) (hgood : α / 2 ≤ S.affineAgreement f z u)
    (hsmall : 1 / (2 : ℝ) ^ (ell - S.rows) < α / 8) :
    ∃ z' : Vector m, ∃ u' : Vector ell, e z' = 1 ∧
      S.affineAgreement f z' u' = S.affineAgreement f z u ∧
      ∀ M, S.Contains M → evaluate M z' + u' = evaluate M z + u := by
  let F : (Vector m →ₗ[F2] Vector ell) → Vector ell :=
    fun N => f (LinearMap.toMatrix' N)
  have hfold' : ∀ (h : S.rowMap.ker) N,
      F (AffineWitness.shift e h N) = F N + h := by
    intro h N
    have hs : LinearMap.toMatrix' (AffineWitness.shift e h N) =
        LinearMap.toMatrix' N + rankOne h (functionalRow e) := by
      simpa only [Matrix.toLin'_toMatrix'] using toMatrix_shift e h (LinearMap.toMatrix' N)
    exact (congrArg f hs).trans (hfold h (LinearMap.toMatrix' N))
  have hgood' := hgood
  rw [S.affineAgreement_eq_linear_ratio M₀ hM₀ f z u] at hgood'
  obtain ⟨z', u', he, ht⟩ := AffineWitness.first_bit_witness e S.rowMap S.columnSpan
    (Matrix.toLin' M₀) z u F hfold' α hα hgood' hsmall
  refine ⟨z', u', he, S.affineAgreement_eq_of_linear_target_eq M₀ hM₀ f z z' u u' ht, ?_⟩
  intro M hM
  exact ht (Matrix.toLin' M) ((S.contains_iff_inSlice M₀ hM₀ M).mp hM)

end Slice
end
end UniqueGamesTheorem.Inverse.Shortcode

end

section

/-!
Fixed-length descriptions for the row-erasure union bound. Row and column
equation lists are padded with zero equations. Targets retain both the linear
coefficient and the affine intercept. Thus the finite description count is
exactly `2^((2r+1)(ell+m))`, including descriptions with empty solution sets.
-/

namespace UniqueGamesTheorem.Inverse.RowErasureDescriptions

open UniqueGamesTheorem.Inverse.Shortcode
open scoped BigOperators

noncomputable section

/-- A row map is represented by all its binary matrix coefficients. -/
abbrev RowMap (ell r : ℕ) := Fin r → Vector ell

/-- Ordered padded row coefficients, row values, column coefficients, column
values, affine coefficient, and affine intercept. Redundant descriptions are
intentional: counting descriptions provides an upper bound on distinct slices. -/
abbrev Description (ell m r : ℕ) :=
  (Fin r → Vector ell) × (Fin r → Vector m) ×
    (Fin r → Vector m) × (Fin r → Vector ell) × Vector m × Vector ell

theorem card_vector (n : ℕ) : Fintype.card (Vector n) = 2 ^ n := by
  simp [Shortcode.Vector, F2]

theorem card_rowMap (ell r : ℕ) : Fintype.card (RowMap ell r) = 2 ^ (ell * r) := by
  simp [RowMap, ← pow_mul]

theorem card_description (ell m r : ℕ) :
    Fintype.card (Description ell m r) = 2 ^ ((2 * r + 1) * (ell + m)) := by
  simp only [Description, Fintype.card_prod, Fintype.card_fun, Fintype.card_fin,
    ← pow_mul, ← pow_add]
  congr 1
  ring

def Description.toSlice {ell m r : ℕ} (d : Description ell m r) : Slice ell m where
  rows := r
  columns := r
  rowCoefficient := d.1
  rowValue := d.2.1
  columnCoefficient := d.2.2.1
  columnValue := d.2.2.2.1

def Description.coefficient {ell m r : ℕ} (d : Description ell m r) : Vector m :=
  d.2.2.2.2.1

def Description.intercept {ell m r : ℕ} (d : Description ell m r) : Vector ell :=
  d.2.2.2.2.2

/-- Add vacuous equations after the original finite list. -/
def padZero {n r : ℕ} {V : Type*} [Zero V] (f : Fin n → V) : Fin r → V :=
  fun i => if h : i.val < n then f ⟨i.val, h⟩ else 0

def padSlice {ell m : ℕ} (S : Slice ell m) (r : ℕ) : Slice ell m where
  rows := r
  columns := r
  rowCoefficient := padZero S.rowCoefficient
  rowValue := padZero S.rowValue
  columnCoefficient := padZero S.columnCoefficient
  columnValue := padZero S.columnValue

theorem padSlice_contains_iff {ell m r : ℕ} (S : Slice ell m)
    (hrows : S.rows ≤ r) (hcols : S.columns ≤ r) (M : Mat ell m) :
    (padSlice S r).Contains M ↔ S.Contains M := by
  classical
  constructor
  · rintro ⟨hr, hc⟩
    constructor
    · intro i j
      have h := hr ⟨i.val, lt_of_lt_of_le i.isLt hrows⟩ j
      simpa [padSlice, padZero, i.isLt] using h
    · intro i
      have h := hc ⟨i.val, lt_of_lt_of_le i.isLt hcols⟩
      simpa [padSlice, padZero, i.isLt] using h
  · rintro ⟨hr, hc⟩
    constructor
    · intro i j
      by_cases hi : i.val < S.rows
      · simpa [padSlice, padZero, hi] using hr ⟨i.val, hi⟩ j
      · simp [padSlice, padZero, hi]
    · intro i
      by_cases hi : i.val < S.columns
      · simpa [padSlice, padZero, hi] using hc ⟨i.val, hi⟩
      · simp [padSlice, padZero, hi]

theorem padSlice_points {ell m r : ℕ} (S : Slice ell m)
    (hrows : S.rows ≤ r) (hcols : S.columns ≤ r) :
    (padSlice S r).points = S.points := by
  classical
  ext M
  simp [Slice.points, padSlice_contains_iff S hrows hcols M]

theorem padSlice_affineAgreement {ell m r : ℕ} (S : Slice ell m)
    (hrows : S.rows ≤ r) (hcols : S.columns ≤ r)
    (f : Mat ell m → Vector ell) (z : Vector m) (u : Vector ell) :
    (padSlice S r).affineAgreement f z u = S.affineAgreement f z u := by
  simp only [Slice.affineAgreement, padSlice_points S hrows hcols]

def describe {ell m r : ℕ} (S : Slice ell m)
    (z : Vector m) (u : Vector ell) : Description ell m r :=
  (padZero S.rowCoefficient, padZero S.rowValue,
    padZero S.columnCoefficient, padZero S.columnValue, z, u)

@[simp] theorem describe_toSlice {ell m r : ℕ} (S : Slice ell m)
    (z : Vector m) (u : Vector ell) :
    (describe (r := r) S z u).toSlice = padSlice S r := rfl

@[simp] theorem describe_coefficient {ell m r : ℕ} (S : Slice ell m)
    (z : Vector m) (u : Vector ell) : (describe (r := r) S z u).coefficient = z := rfl

@[simp] theorem describe_intercept {ell m r : ℕ} (S : Slice ell m)
    (z : Vector m) (u : Vector ell) : (describe (r := r) S z u).intercept = u := rfl

/-- Every slice/target returned by the bounded inverse theorem has a fixed-size
description with the same solution set and exactly the same agreement. -/
theorem exists_description {ell m r : ℕ} (S : Slice ell m)
    (hrows : S.rows ≤ r) (hcols : S.columns ≤ r)
    (z : Vector m) (u : Vector ell) :
    ∃ d : Description ell m r, d.toSlice.points = S.points ∧
      d.coefficient = z ∧ d.intercept = u := by
  refine ⟨describe S z u, ?_, rfl, rfl⟩
  exact padSlice_points S hrows hcols

end
end UniqueGamesTheorem.Inverse.RowErasureDescriptions

end

end OAI
