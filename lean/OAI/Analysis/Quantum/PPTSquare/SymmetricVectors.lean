import OAI.Analysis.Quantum.PPTSquare.TensorPositivity

namespace OAI

noncomputable section
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
open Matrix
namespace TensorCriterion
open ChannelCompletion
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
open Matrix

def symWeight (t : Fin 10) : ℂ := if (symPair t).1 = (symPair t).2 then 1 else rt

def xhat (x : Fin 4 → ℂ) : Fin 10 → ℂ :=
  fun t => symWeight t * x (symPair t).1 * x (symPair t).2

lemma symWeight_ne (t : Fin 10) : symWeight t ≠ 0 := by
  unfold symWeight
  split_ifs <;> simp [rt_ne]

lemma U_xhat_row0 (x : Fin 4 → ℂ) (b : Fin 4) :
    U.mulVec (xhat x) (0, b) = x 0 * x b := by
  fin_cases b <;>
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, U, xhat, symWeight, symPair] <;>
    field_simp [rt_ne]

lemma U_xhat_row1 (x : Fin 4 → ℂ) (b : Fin 4) :
    U.mulVec (xhat x) (1, b) = x 1 * x b := by
  fin_cases b <;>
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, U, xhat, symWeight, symPair] <;>
    field_simp [rt_ne]

lemma U_xhat_row2 (x : Fin 4 → ℂ) (b : Fin 4) :
    U.mulVec (xhat x) (2, b) = x 2 * x b := by
  fin_cases b <;>
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, U, xhat, symWeight, symPair] <;>
    field_simp [rt_ne]

lemma U_xhat_row3 (x : Fin 4 → ℂ) (b : Fin 4) :
    U.mulVec (xhat x) (3, b) = x 3 * x b := by
  fin_cases b <;>
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, U, xhat, symWeight, symPair] <;>
    field_simp [rt_ne]

lemma U_xhat (x : Fin 4 → ℂ) : U.mulVec (xhat x) = product x x := by
  ext ⟨a,b⟩
  fin_cases a
  · exact U_xhat_row0 x b
  · exact U_xhat_row1 x b
  · exact U_xhat_row2 x b
  · exact U_xhat_row3 x b

lemma xhat_source (x : Fin 4 → ℂ) : xhat x = Uᴴ.mulVec (product x x) := by
  ext t
  fin_cases t <;>
    simp [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Fin.sum_univ_succ,
      Matrix.conjTranspose_apply, U, xhat, symWeight, symPair, product,
      star_inv₀, rt_star, mul_comm, mul_left_comm, mul_assoc] <;>
    field_simp [rt_ne] <;> ring_nf <;>
    simp only [show rt ^ 2 = 2 by simpa only [pow_two] using rt_sq] <;> ring

variable {n m : Type} [Fintype n] [Fintype m]

omit [Fintype m] in
lemma ad_projector (W : Matrix m n ℂ) (x : n → ℂ) : ad W (projector x) = projector (W.mulVec x) := by
  simp only [ad_apply, projector, Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, Matrix.star_mulVec]

omit [Fintype n] [Fintype m] in
lemma projector_product (x : n → ℂ) (y : m → ℂ) :
    projector (product x y) = projector x ⊗ₖ projector y := by
  ext ⟨i,a⟩ ⟨j,b⟩
  simp only [projector, product, Matrix.vecMulVec_apply, Pi.star_apply,
    Matrix.kronecker_apply, star_mul]
  ring

lemma S_projector (L : Map (Fin 4) (Fin 4)) (x : Fin 4 → ℂ) :
    S L (projector (xhat x)) = compound (L (projector x)) := by
  simp only [S, LinearMap.comp_apply]
  rw [ad_projector, U_xhat, projector_product, tensorMap_kronecker]
  simpa only [ad_apply, Matrix.conjTranspose_conjTranspose] using V_compression (L (projector x))

lemma R_projector (L : Map (Fin 4) (Fin 4)) (x : Fin 4 → ℂ) :
    R L (projector (xhat x)) = K * (compound (L (projector x)))ᵀ * Kᴴ := by
  simp only [R, LinearMap.comp_apply, transposeMap_apply, ad_apply, S_projector]

lemma exterior_projector_pairing (L : Map (Fin 4) (Fin 4)) (x : Fin 4 → ℂ) :
    Matrix.trace (R L (projector (xhat x)) * S L (projector (xhat x))) =
      6 * (L (projector x)).det := by
  rw [R_projector, S_projector, compound_pair_trace]

end TensorCriterion

namespace TensorCriterion
open ChannelCompletion
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
open Matrix

lemma E_isometry : Eᴴ * E = 1 := by
  apply coord_isometry
  intro a b h
  exact Fin.ext (congrArg (fun z : Fin 10 => z.val) h)

lemma composite_apply (L : Map (Fin 4) (Fin 4)) (A : Mat (Fin 10)) :
    Phi2 L (Phi1 L A) = hsAdjoint (R L) (S L Aᵀ) := by
  simp only [Phi1, Phi2, LinearMap.comp_apply, transposeMap_apply, ad_apply,
    Matrix.conjTranspose_conjTranspose]
  congr 1
  calc
    Eᴴ * (E * S L Aᵀ * Eᴴ) * E = (Eᴴ * E) * S L Aᵀ * (Eᴴ * E) := by
      simp only [Matrix.mul_assoc]
    _ = S L Aᵀ := by rw [E_isometry, Matrix.one_mul, Matrix.mul_one]

variable {n m : Type} [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]

lemma choi_trace_pairing (F : Map n m) (A : Mat n) (B : Mat m) :
    Matrix.trace ((A ⊗ₖ B) * choi F) = Matrix.trace (B * F Aᵀ) := by
  induction A using Matrix.induction_on' with
  | h_zero => simp
  | h_add A A' hA hA' =>
    simp [Matrix.add_kronecker, Matrix.add_mul, Matrix.mul_add, hA, hA']
  | h_std_basis i j c =>
    induction B using Matrix.induction_on' with
    | h_zero => simp
    | h_add B B' hB hB' =>
      simp [Matrix.kronecker_add, Matrix.add_mul, hB, hB']
    | h_std_basis a b d =>
      have hb : (Matrix.single i j c)ᵀ = c • Matrix.single j i (1 : ℂ) := by simp
      rw [Matrix.single_kronecker_single, Matrix.trace_single_mul, hb, map_smul,
        Matrix.mul_smul, Matrix.trace_smul, Matrix.trace_single_mul]
      simp only [choi, smul_eq_mul]
      ring

omit [DecidableEq n] in
lemma trace_projector_mul (x : n → ℂ) (A : Mat n) :
    Matrix.trace (projector x * A) = star x ⬝ᵥ A.mulVec x := by
  rw [projector, Matrix.vecMulVec_mul, Matrix.trace_vecMulVec,
    dotProduct_comm, Matrix.dotProduct_mulVec]

lemma Z_psd {L : Map (Fin 4) (Fin 4)} (hL : PPT L) : (Z L).PosSemidef :=
  cp_choi (cp_comp (Phi2_ppt hL).1 (Phi1_ppt hL).1)

lemma Z_trace_pairing {L : Map (Fin 4) (Fin 4)} (hL : PPT L)
    (A B : Mat (Fin 10)) :
    Matrix.trace ((A ⊗ₖ B) * Z L) = Matrix.trace (R L B * S L A) := by
  rw [Z, choi_trace_pairing]
  change Matrix.trace (B * Phi2 L (Phi1 L Aᵀ)) = _
  rw [composite_apply, Matrix.transpose_transpose, trace_hsAdjoint (R_ppt hL).1]

lemma Z_quadratic {L : Map (Fin 4) (Fin 4)} (hL : PPT L) (x : Fin 4 → ℂ) :
    star (product (xhat x) (xhat x)) ⬝ᵥ (Z L).mulVec (product (xhat x) (xhat x)) =
      6 * (L (projector x)).det := by
  rw [← trace_projector_mul, projector_product, Z_trace_pairing hL,
    exterior_projector_pairing]

lemma det_zero_of_rank_lt {B : Mat (Fin 4)} (h : B.rank < 4) : B.det = 0 := by
  by_contra hh
  have hr := Matrix.rank_of_det_ne_zero hh
  simp only [Fintype.card_fin] at hr
  omega

lemma rank_loss_kernel {L : Map (Fin 4) (Fin 4)} (hL : PPT L) (x : Fin 4 → ℂ)
    (h : (L (projector x)).rank < 4) :
    (Z L).mulVec (product (xhat x) (xhat x)) = 0 := by
  apply (Z_psd hL).dotProduct_mulVec_zero_iff.mp
  rw [Z_quadratic hL, det_zero_of_rank_lt h, mul_zero]

lemma Z_ne_zero {L : Map (Fin 4) (Fin 4)} (hL : PPT L)
    (hDef : ∃ y : Fin 4 → ℂ, (L (projector y)).PosDef) : Z L ≠ 0 := by
  obtain ⟨y, hy⟩ := hDef
  intro hZ
  have h := Z_quadratic hL y
  rw [hZ, Matrix.zero_mulVec, dotProduct_zero] at h
  have hd : (L (projector y)).det ≠ 0 := ne_of_gt hy.det_pos
  exact (mul_ne_zero (by norm_num) hd) h.symm

end TensorCriterion

end

end OAI
