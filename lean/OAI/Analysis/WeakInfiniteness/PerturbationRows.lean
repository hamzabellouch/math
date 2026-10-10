import Mathlib
import OAI.Analysis.WeakInfiniteness.FixedRows
import OAI.Analysis.WeakInfiniteness.MatrixHilbert
import OAI.Analysis.WeakInfiniteness.MatrixMaps
import OAI.Analysis.WeakInfiniteness.SupportedCorner

namespace OAI

noncomputable section
open scoped TensorProduct ENNReal ComplexOrder
open UniformSpace
open CStarAlgebra
open scoped NNReal
open scoped TensorProduct ComplexConjugate
open scoped ENNReal InnerProductSpace
open scoped InnerProductSpace
open scoped TensorProduct InnerProductSpace
open Filter Topology
open Complex selfAdjoint
open scoped ComplexOrder

namespace WeakPureInfiniteness

noncomputable section

open scoped CStarAlgebra

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable {n : ℕ}

local instance matrixRealModulePerturbRows {m : Type*} [Fintype m] :
    Module ℝ (CStarMatrix m m A) := Module.complexToReal _

omit [PartialOrder A] [StarOrderedRing A] in
lemma diagonal_singleton (X : CStarMatrix (Fin 1) (Fin 1) A) :
    diagonalCopies 1 (matrixSingletonHom X)=X := by
  ext i j
  have hi : i=0 := Subsingleton.elim _ _
  have hj : j=0 := Subsingleton.elim _ _
  subst i; subst j
  rfl

omit [PartialOrder A] [StarOrderedRing A] in
lemma singleton_diagonal (x : A) : matrixSingletonHom (diagonalCopies 1 x)=x := rfl

lemma norm_diagonalCopies_le (m : ℕ) (x : A) : ‖diagonalCopies m x‖ ≤ ‖x‖ :=
  NonUnitalStarAlgHom.norm_apply_le (diagonalHom m) x

lemma norm_row_test_le (R S : CStarMatrix (Fin 1) (Fin n) A)
    (w : CStarMatrix (Fin n) (Fin n) A) (hR : ‖R‖ ≤ 1) (hS : ‖S‖ ≤ 1) (hw : ‖w‖ ≤ 1) :
    ‖matrixSingletonHom (-(R*w*S.conjTranspose))‖ ≤ 1 := by
  apply (NonUnitalStarAlgHom.norm_apply_le (matrixSingletonHom (A := A)) _).trans
  rw [norm_neg]
  calc
    ‖R*w*S.conjTranspose‖ ≤ (‖R‖*‖w‖)*‖S.conjTranspose‖ :=
      (rectangular_norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right
        (rectangular_norm_mul_le R w) (norm_nonneg _))
    _ ≤ (1*1)*1 := by rw [rectangular_norm_conjTranspose]; gcongr
    _ = 1 := by norm_num

omit [PartialOrder A] [StarOrderedRing A] in
lemma rectangular_mul_sub_perturb {m k l : Type*} [Fintype k]
    (L : CStarMatrix m k A) (X Y : CStarMatrix k l A) : L*(X-Y)=L*X-L*Y :=
  Matrix.mul_sub L X Y

omit [PartialOrder A] [StarOrderedRing A] in
lemma rectangular_sub_mul_perturb {m k l : Type*} [Fintype k]
    (X Y : CStarMatrix m k A) (R : CStarMatrix k l A) : (X-Y)*R=X*R-Y*R :=
  Matrix.sub_mul X Y R

omit [PartialOrder A] [StarOrderedRing A] in
lemma rectangular_neg_mul_perturb {m k l : Type*} [Fintype k]
    (L : CStarMatrix m k A) (R : CStarMatrix k l A) : (-L)*R=-(L*R) := Matrix.neg_mul L R

omit [PartialOrder A] [StarOrderedRing A] in
lemma rectangular_mul_neg_perturb {m k l : Type*} [Fintype k]
    (L : CStarMatrix m k A) (R : CStarMatrix k l A) : L*(-R)=-(L*R) := Matrix.mul_neg L R

omit [PartialOrder A] [StarOrderedRing A] in
lemma compress_row_test (L : CStarMatrix (Fin n) (Fin 1) A)
    (K R S : CStarMatrix (Fin 1) (Fin n) A)
    (P Q : CStarMatrix (Fin 1) (Fin 1) A) (E w : CStarMatrix (Fin n) (Fin n) A)
    (hL : L*P*R=E) (hK : S.conjTranspose*Q*K=E) (hw : E*w*E=w) :
    L*(P*(-(R*w*S.conjTranspose))*Q)*K= -w := by
  rw [rectangular_mul_neg_perturb, rectangular_neg_mul_perturb,
    rectangular_mul_neg_perturb, rectangular_neg_mul_perturb]
  congr 1
  calc
    L*(P*(R*w*S.conjTranspose)*Q)*K = (L*P*R)*w*(S.conjTranspose*Q*K) := by
      simp only [rectangular_mul_assoc]
    _ = w := by rw [hL,hK,hw]

lemma norm_representation_compression_le {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H]
    (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H))
    (L : CStarMatrix (Fin n) (Fin 1) A) (K : CStarMatrix (Fin 1) (Fin n) A)
    (X : CStarMatrix (Fin 1) (Fin 1) A) (hL : ‖L‖ ≤ 1) (hK : ‖K‖ ≤ 1) :
    ‖matrixRepresentation π (Fin n) (L*X*K)‖ ≤ ‖π (matrixSingletonHom X)‖ := by
  have hX : ‖rectangularMap π X‖ = ‖π (matrixSingletonHom X)‖ := by
    have hh := NonUnitalStarAlgHom.norm_map matrixSingletonHom matrixSingletonHom_injective
      (rectangularMap π X)
    exact hh.symm
  calc
    _ ≤ ‖rectangularMap π (L*X*K)‖ := NonUnitalStarAlgHom.norm_apply_le (matrixActionHom (n := Fin n) (H := H)) (rectangularMap π (L*X*K))
    _ = ‖rectangularMap π L*rectangularMap π X*rectangularMap π K‖ := by rw [rectangularMap_mul, rectangularMap_mul]
    _ ≤ ‖rectangularMap π L‖*‖rectangularMap π X‖*‖rectangularMap π K‖ :=
      (rectangular_norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right
        (rectangular_norm_mul_le _ _) (norm_nonneg _))
    _ ≤ 1*‖π (matrixSingletonHom X)‖*1 := by
      rw [hX]
      gcongr
      · exact (rectangularMap_norm_le π L).trans hL
      · exact (rectangularMap_norm_le π K).trans hK
    _ = ‖π (matrixSingletonHom X)‖ := by ring

lemma supported_testing_element (c : A) {α : ℝ} (hα : 0 < α)
    (R S : CStarMatrix (Fin 1) (Fin n) A)
    (hR : R.conjTranspose*R=diagonalCopies n (cfcₙ (spectralRamp (α/4)) c))
    (hS : S.conjTranspose*S=diagonalCopies n (cfcₙ (spectralRamp (α/4)) c))
    (X : CStarMatrix (Fin 1) (Fin 1) A) (z : ℂ) :
    let e := diagonalCopies n (cfcₙ (spectralRamp (α/16)) c)
    e*(z • (R.conjTranspose*X*S))=z • (R.conjTranspose*X*S) ∧
      (z • (R.conjTranspose*X*S))*e=z • (R.conjTranspose*X*S) := by
  dsimp only
  have hl := fixed_row_shallow_support c hα R hR
  have hr := congrArg CStarMatrix.conjTranspose (fixed_row_shallow_support c hα S hS)
  have he : IsSelfAdjoint (diagonalCopies n (cfcₙ (spectralRamp (α/16)) c)) := by
    exact (cfcₙ_predicate (spectralRamp (α/16)) c).map (diagonalHom n)
  rw [rectangular_star_mul, rectangular_conjTranspose_conjTranspose] at hr
  change S*star (diagonalCopies n (cfcₙ (spectralRamp (α/16)) c))=S at hr
  rw [he.star_eq] at hr
  constructor
  · rw [mul_smul_comm, ← rectangular_mul_assoc, ← rectangular_mul_assoc, hl]
  · rw [smul_mul_assoc, rectangular_mul_assoc, hr]

end

end WeakPureInfiniteness
end

end OAI
