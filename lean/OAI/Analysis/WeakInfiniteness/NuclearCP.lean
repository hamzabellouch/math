import Mathlib
import OAI.Analysis.WeakInfiniteness.TensorFoundations

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

open scoped CStarAlgebra Topology ComplexOrder

open Filter

universe u v

local instance nuclearMatrixRealModule {A : Type*} [NonUnitalCStarAlgebra A]
    [PartialOrder A] [StarOrderedRing A] {n : Type*} [Fintype n] :
    Module ℝ (CStarMatrix n n A) := Module.complexToReal _

section

variable {A : Type u} {B : Type v} [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
  [PartialOrder A] [StarOrderedRing A] [PartialOrder B] [StarOrderedRing B]

variable {n : Type*} [Fintype n]

def matrixLinearMap (φ : A →L[ℂ] B) : CStarMatrix n n A →L[ℂ] CStarMatrix n n B where
  toLinearMap := CStarMatrix.mapₗ φ.toLinearMap
  cont := by
    change Continuous (fun M : n → n → A => fun i j => φ (M i j))
    exact continuous_pi fun i => continuous_pi fun j =>
      φ.continuous.comp ((continuous_apply j).comp (continuous_apply i))

omit [PartialOrder A] [StarOrderedRing A] [PartialOrder B] [StarOrderedRing B] [Fintype n] in
@[simp] lemma matrixLinearMap_apply (φ : A →L[ℂ] B) (M : CStarMatrix n n A) (i j : n) :
    matrixLinearMap φ M i j = φ (M i j) := rfl

lemma matrixLinearMap_nonneg {φ : A →L[ℂ] B} (hφ : CompletelyPositive φ)
    {M : CStarMatrix n n A} (hM : 0 ≤ M) : 0 ≤ matrixLinearMap φ M :=
  hφ.toMap.map_cstarMatrix_nonneg M hM

lemma matrixLinearMap_mono {φ : A →L[ℂ] B} (hφ : CompletelyPositive φ) :
    Monotone (matrixLinearMap (n := n) φ) := by
  intro M N hMN
  have hm := matrixLinearMap_nonneg hφ (sub_nonneg.mpr hMN)
  simpa only [map_sub,sub_nonneg] using hm

variable [DecidableEq n]

def matrixDiagonalHom : A →⋆ₙₐ[ℂ] CStarMatrix n n A where
  toFun a := CStarMatrix.ofMatrix (Matrix.diagonal fun _ => a)
  map_zero' := by ext i j; simp
  map_add' a b := by ext i j; simp [Matrix.diagonal_apply]; split_ifs <;> simp
  map_mul' a b := by
    change Matrix.diagonal (fun _ : n => a*b)=Matrix.diagonal (fun _ : n => a)*Matrix.diagonal (fun _ : n => b)
    rw [Matrix.diagonal_mul_diagonal]
  map_smul' c a := by ext i j; simp [Matrix.diagonal_apply]
  map_star' a := by
    ext i j
    simp only [CStarMatrix.ofMatrix_apply, CStarMatrix.star_eq_conjTranspose,
      CStarMatrix.conjTranspose_apply,Matrix.diagonal_apply]
    split_ifs <;> simp_all

omit [PartialOrder A] [StarOrderedRing A] [PartialOrder B] [StarOrderedRing B] in
@[simp] lemma matrixLinearMap_diagonal (φ : A →L[ℂ] B) (a : A) :
    matrixLinearMap φ (matrixDiagonalHom (n := n) a)=matrixDiagonalHom (n := n) (φ a) := by
  ext i j
  simp only [matrixLinearMap_apply,matrixDiagonalHom,NonUnitalStarAlgHom.coe_mk,
    CStarMatrix.ofMatrix_apply,Matrix.diagonal_apply]
  split_ifs <;> simp

lemma matrix_mul_diagonal_tendsto (M : CStarMatrix n n A) :
    Tendsto (fun e => M * matrixDiagonalHom (n := n) e)
      (CStarAlgebra.approximateUnit A) (𝓝 M) := by
  have he : (fun e => M * matrixDiagonalHom (n := n) e) =
      fun e => CStarMatrix.ofMatrix (fun i j => M i j * e) := by
    funext e
    ext i j
    change ((CStarMatrix.ofMatrix.symm M : Matrix n n A) * Matrix.diagonal (fun _ : n => e)) i j = M i j * e
    rw [Matrix.mul_diagonal]
    rfl
  rw [he]
  change Tendsto (fun e => fun i j => M i j * e) _ (𝓝 (fun i j => M i j))
  exact tendsto_pi_nhds.mpr fun i => tendsto_pi_nhds.mpr fun j =>
    (CStarAlgebra.increasingApproximateUnit A).tendsto_mul_left (M i j)

lemma norm_matrixLinearMap_nonneg_le {φ : A →L[ℂ] B} (hφ : CompletelyPositive φ)
    (M : CStarMatrix n n A) (hM : 0 ≤ M) :
    ‖matrixLinearMap φ M‖ ≤ ‖φ‖ * ‖M‖ := by
  let F := matrixLinearMap (n := n) φ
  let l := CStarAlgebra.approximateUnit A
  have hl := CStarAlgebra.increasingApproximateUnit A
  let : l.NeBot := hl.toIsApproximateUnit.neBot
  have ht := matrix_mul_diagonal_tendsto (CFC.sqrt M)
  have hsq : star (CFC.sqrt M)*CFC.sqrt M=M := by
    rw [(CFC.sqrt_nonneg M).star_eq,CFC.sqrt_mul_sqrt_self M hM]
  have ht' : Tendsto (fun e => star (matrixDiagonalHom (n := n) e)*M*matrixDiagonalHom (n := n) e)
      l (𝓝 M) := by
    convert ht.star.mul ht using 1
    · ext e
      simp only [star_mul,mul_assoc]
      rw [← mul_assoc (star (CFC.sqrt M)),hsq]
    · rw [hsq]
  apply le_of_tendsto (F.continuous.tendsto M |>.comp ht' |>.norm)
  filter_upwards [hl.eventually_norm] with e he
  let D := matrixDiagonalHom (n := n) e
  have hpos : 0 ≤ star D*M*D := star_left_conjugate_nonneg hM _
  have hle := matrixLinearMap_mono hφ
    (CStarAlgebra.star_left_conjugate_le_norm_smul D M hM.isSelfAdjoint)
  have hn : ‖F (star D*D)‖ ≤ ‖φ‖ := by
    have hd : F (star D*D)=matrixDiagonalHom (n := n) (φ (star e*e)) := by
      simp only [D,F,← map_star,← map_mul,matrixLinearMap_diagonal]
    rw [hd]
    calc
      _ ≤ ‖φ (star e*e)‖ := NonUnitalStarAlgHom.norm_apply_le _ _
      _ ≤ ‖φ‖ * ‖star e*e‖ := φ.le_opNorm _
      _ ≤ ‖φ‖ * 1 := by
        gcongr
        rw [CStarRing.norm_star_mul_self]
        nlinarith [norm_nonneg e]
      _ = ‖φ‖ := mul_one _
  calc
    ‖F (star D*M*D)‖ ≤ ‖F (‖M‖ • (star D*D))‖ :=
      CStarAlgebra.norm_le_norm_of_le_of_nonneg hle (matrixLinearMap_nonneg hφ hpos)
    _ = ‖M‖ * ‖F (star D*D)‖ := by
      change ‖F ((‖M‖ : ℂ) • (star D*D))‖ = _
      rw [map_smul,norm_smul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (norm_nonneg M)]
    _ ≤ ‖M‖ * ‖φ‖ := mul_le_mul_of_nonneg_left hn (norm_nonneg M)
    _ = ‖φ‖ * ‖M‖ := mul_comm _ _

lemma norm_matrixLinearMap_le {φ : A →L[ℂ] B} (hφ : CompletelyPositive φ)
    (M : CStarMatrix n n A) : ‖matrixLinearMap φ M‖ ≤ (4*‖φ‖)*‖M‖ := by
  obtain ⟨x,hx,hxn,rfl⟩ := CStarAlgebra.exists_sum_four_nonneg M
  rw [map_sum]
  apply (norm_sum_le _ _).trans
  calc
    (∑ i : Fin 4, ‖matrixLinearMap φ (Complex.I ^ (i : ℕ) • x i)‖) ≤
        ∑ _i : Fin 4, ‖φ‖ * ‖∑ i : Fin 4, Complex.I ^ (i : ℕ) • x i‖ := by
      apply Finset.sum_le_sum
      intro i _
      simp only [map_smul,norm_smul,norm_pow,Complex.norm_I,one_pow,one_mul]
      exact (norm_matrixLinearMap_nonneg_le hφ _ (hx i)).trans
        (mul_le_mul_of_nonneg_left (hxn i) (norm_nonneg φ))
    _ = _ := by simp; ring

end

end

end WeakPureInfiniteness
end

end OAI
