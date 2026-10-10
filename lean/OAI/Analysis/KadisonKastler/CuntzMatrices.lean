import OAI.Analysis.KadisonKastler.Algebra
import OAI.Analysis.KadisonKastler.CompletelyBounded
import Mathlib.Analysis.CStarAlgebra.Hom

namespace OAI

/-! # Matrix amplification using common isometries

A finite Cuntz family gives an actual star equivalence between the ambient
operator algebra and its matrix amplification. If its isometries belong to
two concrete algebras, the same equivalence identifies both matrix unit
balls with their original unit balls.
-/

namespace KadisonKastler

open scoped BigOperators CStarAlgebra

noncomputable section

variable {H n : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [Fintype n] [DecidableEq n]

/-- A finite family of isometries with orthogonal ranges summing to one. -/
structure CuntzFamily (n : Type*) [Fintype n] [DecidableEq n] (H : Type*)
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] where
  entry : n → (H →L[ℂ] H)
  orthogonal : ∀ i j, star (entry i) * entry j = if i = j then 1 else 0
  total : ∑ i, entry i * star (entry i) = 1

namespace CuntzFamily

local instance : PartialOrder (H →L[ℂ] H) := CStarAlgebra.spectralOrder _
local instance : StarOrderedRing (H →L[ℂ] H) := CStarAlgebra.spectralOrderedRing _

variable (S : CuntzFamily n H)

def matrix (T : H →L[ℂ] H) : CStarMatrix n n (H →L[ℂ] H) :=
  fun i j => star (S.entry i) * T * S.entry j

def assemble (X : CStarMatrix n n (H →L[ℂ] H)) : H →L[ℂ] H :=
  ∑ i, ∑ j, S.entry i * X i j * star (S.entry j)

theorem assemble_matrix (T : H →L[ℂ] H) : S.assemble (S.matrix T) = T := by
  have hterm (i j : n) :
      S.entry i * (star (S.entry i) * T * S.entry j) * star (S.entry j) =
        (S.entry i * star (S.entry i)) * T * (S.entry j * star (S.entry j)) := by
    noncomm_ring
  simp only [assemble, matrix, hterm]
  simp_rw [← Finset.mul_sum, S.total, mul_one]
  rw [← Finset.sum_mul, S.total, one_mul]

theorem matrix_assemble (X : CStarMatrix n n (H →L[ℂ] H)) : S.matrix (S.assemble X) = X := by
  apply Matrix.ext
  intro i j
  change star (S.entry i) * (∑ k, ∑ l, S.entry k * X k l * star (S.entry l)) * S.entry j = X i j
  simp only [Finset.mul_sum, Finset.sum_mul]
  have hterm (k l : n) : star (S.entry i) * (S.entry k * X k l * star (S.entry l)) * S.entry j =
      (star (S.entry i) * S.entry k) * X k l * (star (S.entry l) * S.entry j) := by
    noncomm_ring
  simp only [hterm, S.orthogonal]
  simp

theorem matrix_mul (T U : H →L[ℂ] H) : S.matrix (T * U) = S.matrix T * S.matrix U := by
  apply Matrix.ext
  intro i j
  change star (S.entry i) * (T * U) * S.entry j =
    ∑ k, (star (S.entry i) * T * S.entry k) * (star (S.entry k) * U * S.entry j)
  have hterm (k : n) :
      (star (S.entry i) * T * S.entry k) * (star (S.entry k) * U * S.entry j) =
        (star (S.entry i) * T) * (S.entry k * star (S.entry k)) * (U * S.entry j) := by
    noncomm_ring
  simp only [hterm]
  rw [← Finset.sum_mul, ← Finset.mul_sum, S.total, mul_one]
  noncomm_ring

def matrixHom : (H →L[ℂ] H) →⋆ₐ[ℂ] CStarMatrix n n (H →L[ℂ] H) where
  toFun := S.matrix
  map_one' := by ext i j; simp [matrix, S.orthogonal, CStarMatrix.one_apply]
  map_mul' := S.matrix_mul
  map_zero' := by ext i j; simp [matrix]
  map_add' T U := by ext i j; simp [matrix, mul_add, add_mul]
  commutes' c := by
    ext i j
    simp only [matrix, Algebra.algebraMap_eq_smul_one, mul_smul_comm, smul_mul_assoc,
      mul_one, S.orthogonal, CStarMatrix.algebraMap_apply]
    split_ifs <;> simp
  map_star' T := by ext i j; simp [matrix, CStarMatrix.star_apply, star_mul, mul_assoc]

theorem matrixHom_injective : Function.Injective S.matrixHom := by
  intro T U h
  have hh := congrArg S.assemble h
  simpa only [matrixHom, StarAlgHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk,
    S.assemble_matrix] using hh

def matrixEquiv : (H →L[ℂ] H) ≃⋆ₐ[ℂ] CStarMatrix n n (H →L[ℂ] H) :=
  StarAlgEquiv.ofBijective S.matrixHom
    ⟨S.matrixHom_injective, fun X => ⟨S.assemble X, S.matrix_assemble X⟩⟩

@[simp] theorem norm_matrix (T : H →L[ℂ] H) : ‖S.matrix T‖ = ‖T‖ :=
  NonUnitalStarAlgHom.norm_map S.matrixHom S.matrixHom_injective T

@[simp] theorem norm_assemble (X : CStarMatrix n n (H →L[ℂ] H)) : ‖S.assemble X‖ = ‖X‖ := by
  rw [← S.norm_matrix, S.matrix_assemble]

theorem matrix_mem (M : VonNeumannAlgebra H) (hS : ∀ i, S.entry i ∈ M)
    {T : H →L[ℂ] H} (hT : T ∈ M) (i j : n) : S.matrix T i j ∈ M :=
  M.mul_mem (M.mul_mem (M.toStarSubalgebra.star_mem' (hS i)) hT) (hS j)

theorem assemble_mem (M : VonNeumannAlgebra H) (hS : ∀ i, S.entry i ∈ M)
    (X : CStarMatrix n n (H →L[ℂ] H)) (hX : ∀ i j, X i j ∈ M) : S.assemble X ∈ M := by
  exact M.sum_mem fun i _ => M.sum_mem fun j _ =>
    M.mul_mem (M.mul_mem (hS i) (hX i j)) (M.toStarSubalgebra.star_mem' (hS j))

/-- The concrete matrix unit ball uses the C*-matrix norm. -/
def matrixUnitBall (M : VonNeumannAlgebra H) : Set (CStarMatrix n n (H →L[ℂ] H)) :=
  {X | (∀ i j, X i j ∈ M) ∧ ‖X‖ ≤ 1}

theorem matrixUnitBall_image (M : VonNeumannAlgebra H) (hS : ∀ i, S.entry i ∈ M) :
    S.matrix '' unitBall M = matrixUnitBall (n := n) M := by
  ext X
  constructor
  · rintro ⟨T, hT, rfl⟩
    exact ⟨S.matrix_mem M hS hT.1, (S.norm_matrix T).le.trans hT.2⟩
  · rintro ⟨hX, hn⟩
    exact ⟨S.assemble X,
      ⟨S.assemble_mem M hS X hX, (S.norm_assemble X).le.trans hn⟩,
      S.matrix_assemble X⟩

/-- The matrix-level Hausdorff distance is exactly the ordinary distance
when the same Cuntz family belongs to both algebras. -/
theorem matrix_hausdorffDist_eq (M N : VonNeumannAlgebra H)
    (hM : ∀ i, S.entry i ∈ M) (hN : ∀ i, S.entry i ∈ N) :
    Metric.hausdorffDist (matrixUnitBall (n := n) M) (matrixUnitBall (n := n) N) =
      kkDistance M N := by
  rw [← S.matrixUnitBall_image M hM, ← S.matrixUnitBall_image N hN]
  exact Metric.hausdorffDist_image
    (NonUnitalStarAlgHom.isometry S.matrixHom S.matrixHom_injective)

/-- Common isometries transport an ordinary unit-ball approximant to a
matrix unit-ball approximant with precisely the same error. -/
theorem exists_matrix_unitBall_approx (M N : VonNeumannAlgebra H)
    (hM : ∀ i, S.entry i ∈ M) (hN : ∀ i, S.entry i ∈ N)
    {r : ℝ} (hr : kkDistance M N < r)
    (X : CStarMatrix n n (H →L[ℂ] H)) (hX : ∀ i j, X i j ∈ M) (hXnorm : ‖X‖ ≤ 1) :
    ∃ Y : CStarMatrix n n (H →L[ℂ] H), (∀ i j, Y i j ∈ N) ∧
      ‖Y‖ ≤ 1 ∧ ‖X - Y‖ < r := by
  obtain ⟨T, hT, hclose⟩ := exists_unitBall_approx
    ⟨S.assemble_mem M hM X hX, (S.norm_assemble X).le.trans hXnorm⟩ hr
  refine ⟨S.matrix T, S.matrix_mem N hN hT.1, (S.norm_matrix T).le.trans hT.2, ?_⟩
  have he : X - S.matrix T = S.matrix (S.assemble X - T) := by
    rw [show S.matrix (S.assemble X - T) = S.matrix (S.assemble X) - S.matrix T from
      map_sub S.matrixHom _ _, S.matrix_assemble]
  rw [he, S.norm_matrix]
  exact hclose

end CuntzFamily

end

end KadisonKastler

end OAI
