import OAI.Probability.EntangledGames.ExposureChain

namespace OAI

universe u_m u_n u_R u_A u_B u_Z

noncomputable section
open scoped BigOperators MatrixOrder ComplexOrder
open Matrix
namespace ThresholdParallelRepetition.QuantumSampling
section Blocks
variable {m : Type u_m} {n : Type u_n} {R : Type u_R} [Fintype m] [Fintype n] [Fintype R] [DecidableEq R]
lemma trace_blockDiagonal (C : R → Matrix m m ℂ) :
    Matrix.trace (Matrix.blockDiagonal C) = ∑ r, Matrix.trace (C r) := by
  simp only [Matrix.trace, Matrix.diag, Fintype.sum_prod_type, Matrix.blockDiagonal_apply_eq]
  exact Finset.sum_comm

lemma hsSq_blockDiagonal (C : R → Matrix m n ℂ) :
    hsSq (Matrix.blockDiagonal C) = ∑ r, hsSq (C r) := by
  simp only [hsSq_eq_trace, Matrix.blockDiagonal_conjTranspose, ← Matrix.blockDiagonal_mul,
    trace_blockDiagonal, Complex.re_sum]

lemma prob_blockDiagonal (C : R → Matrix m n ℂ) (A : R → Matrix m m ℂ)
    (B : R → Matrix n n ℂ) :
    prob (Matrix.blockDiagonal C) (Matrix.blockDiagonal A) (Matrix.blockDiagonal B) =
      ∑ r, prob (C r) (A r) (B r) := by
  simp only [prob, eval_eq_trace, Matrix.blockDiagonal_conjTranspose, ← Matrix.blockDiagonal_mul,
    Matrix.blockDiagonal_transpose, trace_blockDiagonal, Complex.re_sum]

variable [DecidableEq m]
lemma posSemidef_blockDiagonal (A : R → Matrix m m ℂ) (hA : ∀ r, (A r).PosSemidef) :
    (Matrix.blockDiagonal A).PosSemidef := by
  let B := Matrix.blockDiagonal (fun r => CFC.sqrt (A r))
  have he : Bᴴ*B = Matrix.blockDiagonal A := by
    simp only [B, Matrix.blockDiagonal_conjTranspose, ← Matrix.blockDiagonal_mul]
    congr 1
    funext r
    rw [(Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg (A r))).isHermitian.eq,
      CFC.sqrt_mul_sqrt_self _ (hA r).nonneg]
  rw [← he]
  exact Matrix.posSemidef_conjTranspose_mul_self B

variable {A : Type u_A} {B : Type u_B} [Fintype A] [Fintype B] [DecidableEq n]
def POVM.blocks (P : R → POVM m A) : POVM (m×R) A where
  effect a := Matrix.blockDiagonal (fun r => (P r).effect a)
  pos a := posSemidef_blockDiagonal _ (fun r => (P r).pos a)
  total := by
    change (∑ a, (Matrix.blockDiagonalAddMonoidHom m m R ℂ) (fun r => (P r).effect a)) = _
    rw [← map_sum]
    have he : (∑ a, fun r => (P r).effect a) = 1 := by
      funext r; simpa only [Finset.sum_apply, Pi.one_apply] using (P r).total
    rw [he]
    exact Matrix.blockDiagonal_one

lemma payoff_blockDiagonal (C : R → Matrix m n ℂ) (P : R → POVM m A) (Q : R → POVM n B)
    (V : A → B → Bool) :
    payoff (Matrix.blockDiagonal C) (POVM.blocks P) (POVM.blocks Q) V =
      ∑ r, payoff (C r) (P r) (Q r) V := by
  simp only [payoff, POVM.blocks, prob_blockDiagonal]
  calc
    _ = ∑ a, ∑ b, ∑ r, if V a b then prob (C r) ((P r).effect a) ((Q r).effect b) else 0 := by
      apply Finset.sum_congr rfl; intro a _
      apply Finset.sum_congr rfl; intro b _
      split <;> simp_all
    _ = _ := by
      conv_rhs =>
        rw [Finset.sum_comm]
        arg 2
        ext a
        rw [Finset.sum_comm]
end Blocks

section Normalization
open scoped Matrix.Norms.Frobenius
variable {m : Type u_m} {n : Type u_n} [Fintype m] [Fintype n]
lemma hsSq_eq_zero_iff (C : Matrix m n ℂ) : hsSq C = 0 ↔ C = 0 := by
  constructor
  · intro h
    apply norm_eq_zero.mp
    rw [norm_eq_sqrt_hsSq, h, Real.sqrt_zero]
  · rintro rfl; exact hsSq_zero

def unitize (C D : Matrix m n ℂ) : Matrix m n ℂ :=
  if hsSq C = 0 then D else (Real.sqrt (hsSq C))⁻¹ • C

lemma hsSq_unitize (C D : Matrix m n ℂ) (hD : hsSq D = 1) : hsSq (unitize C D) = 1 := by
  unfold unitize
  split_ifs with h
  · exact hD
  · rw [hsSq_smul, inv_pow, Real.sq_sqrt (hsSq_nonneg C)]
    exact inv_mul_cancel₀ h

lemma unitize_distance (C D : Matrix m n ℂ) (hD : hsSq D = 1) :
    hsSq (C-unitize C D) = (Real.sqrt (hsSq C)-1)^2 := by
  unfold unitize
  split_ifs with h
  · have hz := (hsSq_eq_zero_iff C).mp h
    simp only [hz, hsSq_zero, Real.sqrt_zero, zero_sub, hsSq_neg, hD]
    norm_num
  · have hs : Real.sqrt (hsSq C) ≠ 0 := (Real.sqrt_pos.2 (lt_of_le_of_ne (hsSq_nonneg C) (Ne.symm h))).ne'
    have he : C - (Real.sqrt (hsSq C))⁻¹ • C = (1-(Real.sqrt (hsSq C))⁻¹) • C := by
      rw [sub_smul, one_smul]
    rw [he, hsSq_smul]
    calc
      _ = (1-(Real.sqrt (hsSq C))⁻¹)^2 * (Real.sqrt (hsSq C))^2 := by rw [Real.sq_sqrt (hsSq_nonneg C)]
      _ = _ := by field_simp

lemma hsSq_difference_unbounded (C D : Matrix m n ℂ) (hD : hsSq D ≤ 1) :
    hsSq C - hsSq D ≤ 2*Real.sqrt (hsSq (C-D)) + hsSq (C-D) := by
  have ht : ‖C‖ ≤ ‖D‖ + ‖C-D‖ := by
    simpa only [norm_sub_rev] using norm_le_insert D C
  have hd := hsSq_le_one_norm hD
  have hc0 := norm_nonneg C
  have hd0 := norm_nonneg D
  have he0 := norm_nonneg (C-D)
  have ht2 := sq_le_sq₀ hc0 (add_nonneg hd0 he0) |>.2 ht
  simp only [norm_eq_sqrt_hsSq] at ht2 hd hd0 he0
  have hmul := mul_le_mul_of_nonneg_right hd he0
  rw [Real.sq_sqrt (hsSq_nonneg C)] at ht2
  nlinarith [Real.sq_sqrt (hsSq_nonneg D), Real.sq_sqrt (hsSq_nonneg (C-D))]
end Normalization

section Payoff
variable {m : Type u_m} {n : Type u_n} {A : Type u_A} {B : Type u_B} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
  [Fintype A] [Fintype B]
lemma payoff_difference_unbounded (C D : Matrix m n ℂ) (P : POVM m A) (Q : POVM n B)
    (V : A → B → Bool) (hD : hsSq D ≤ 1) :
    payoff C P Q V - payoff D P Q V ≤ 2*Real.sqrt (hsSq (C-D)) + hsSq (C-D) := by
  have hsd := (hsSq_mul_contraction (winSqrt_contraction P Q V) (flat D)).trans
    (le_trans (le_of_eq (hsSq_flat D)) hD)
  rw [payoff_eq_hsSq, payoff_eq_hsSq]
  refine (hsSq_difference_unbounded _ _ hsd).trans ?_
  have he : hsSq (CFC.sqrt (winEffect P Q V)*flat C-CFC.sqrt (winEffect P Q V)*flat D) ≤ hsSq (C-D) := by
    rw [← Matrix.mul_sub, ← flat_sub]
    exact (hsSq_mul_contraction (winSqrt_contraction P Q V) _).trans_eq (hsSq_flat _)
  exact add_le_add (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt he) (by norm_num)) he
end Payoff
end ThresholdParallelRepetition.QuantumSampling

end

noncomputable section
open scoped BigOperators MatrixOrder ComplexOrder
open Matrix
namespace ThresholdParallelRepetition.QuantumSampling
variable {m : Type u_m} {n : Type u_n} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

lemma posSemidef_fromBlocks_diag {A : Matrix m m ℂ} {B : Matrix n n ℂ}
    (hA : A.PosSemidef) (hB : B.PosSemidef) :
    (Matrix.fromBlocks A 0 0 B).PosSemidef := by
  let T := Matrix.fromBlocks (CFC.sqrt A) (0 : Matrix m n ℂ) 0 (CFC.sqrt B)
  have he : Tᴴ*T = Matrix.fromBlocks A 0 0 B := by
    simp only [T, Matrix.fromBlocks_conjTranspose, Matrix.conjTranspose_zero,
      Matrix.fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add,
      (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg A)).isHermitian.eq,
      (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg B)).isHermitian.eq,
      CFC.sqrt_mul_sqrt_self _ hA.nonneg, CFC.sqrt_mul_sqrt_self _ hB.nonneg]
  rw [← he]
  exact Matrix.posSemidef_conjTranspose_mul_self T

def squareState (C : Matrix m n ℂ) : Matrix (m⊕n) (m⊕n) ℂ := Matrix.fromBlocks 0 C 0 0

omit [DecidableEq m] [DecidableEq n] in
lemma hsSq_squareState (C : Matrix m n ℂ) : hsSq (squareState C) = hsSq C := by
  simp only [squareState, hsSq_blocks, hsSq_zero, zero_add, add_zero]

omit [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] in
lemma squareState_sub (C D : Matrix m n ℂ) : squareState (C-D) = squareState C-squareState D := by
  simp only [squareState, fromBlocks_sub, sub_self]

variable {A : Type u_A} {B : Type u_B} [Fintype A] [Fintype B]
def POVM.sum (P : POVM m A) (Q : POVM n A) : POVM (m⊕n) A where
  effect a := Matrix.fromBlocks (P.effect a) 0 0 (Q.effect a)
  pos a := posSemidef_fromBlocks_diag (P.pos a) (Q.pos a)
  total := by
    have he : (∑ a, Matrix.fromBlocks (P.effect a) (0 : Matrix m n ℂ) 0 (Q.effect a)) =
        Matrix.fromBlocks (∑ a, P.effect a) 0 0 (∑ a, Q.effect a) := by
      ext i j
      cases i <;> cases j <;> simp [Matrix.sum_apply]
    rw [he, P.total, Q.total, Matrix.fromBlocks_one]

omit [DecidableEq m] [DecidableEq n] in
lemma prob_squareState (C : Matrix m n ℂ) (A₁ : Matrix m m ℂ) (A₂ : Matrix n n ℂ)
    (B₁ : Matrix m m ℂ) (B₂ : Matrix n n ℂ) :
    prob (squareState C) (Matrix.fromBlocks A₁ 0 0 A₂) (Matrix.fromBlocks B₁ 0 0 B₂) =
      prob C A₁ B₂ := by
  simp only [prob, eval_eq_trace, squareState, Matrix.fromBlocks_conjTranspose,
    Matrix.fromBlocks_transpose, Matrix.conjTranspose_zero, Matrix.transpose_zero,
    Matrix.fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add]
  simp only [Matrix.trace, Matrix.diag, Fintype.sum_sum_type, Matrix.fromBlocks_apply₁₁,
    Matrix.fromBlocks_apply₂₂, Matrix.zero_apply, Finset.sum_const_zero, zero_add]

lemma payoff_squareState (C : Matrix m n ℂ) (P : POVM m A) (Q : POVM n B)
    (a₀ : A) (b₀ : B) (V : A → B → Bool) :
    payoff (squareState C) (P.sum (POVM.default a₀)) ((POVM.default b₀).sum Q) V = payoff C P Q V := by
  simp only [payoff, POVM.sum, prob_squareState]
end ThresholdParallelRepetition.QuantumSampling

end

noncomputable section
open scoped BigOperators MatrixOrder ComplexOrder
open Matrix
namespace ThresholdParallelRepetition.QuantumSampling
open FiniteProbability Law
section Stack
variable {m : Type u_m} {n : Type u_n} {R : Type u_R} [Fintype m] [Fintype n] [Fintype R] [DecidableEq R]
def weightedBlock (w : R → ℝ) (C : R → Matrix m n ℂ) : Matrix (m×R) (n×R) ℂ :=
  Matrix.blockDiagonal (fun r => Real.sqrt (w r) • C r)
lemma hsSq_weightedBlock (w : R → ℝ) (hw : ∀ r, 0 ≤ w r) (C : R → Matrix m n ℂ) :
    hsSq (weightedBlock w C) = ∑ r, w r*hsSq (C r) := by
  simp only [weightedBlock, hsSq_blockDiagonal, hsSq_smul, Real.sq_sqrt (hw _)]
omit [Fintype m] [Fintype n] [Fintype R] in
lemma weightedBlock_sub (w : R → ℝ) (C D : R → Matrix m n ℂ) :
    weightedBlock w (fun r => C r-D r) = weightedBlock w C-weightedBlock w D := by
  simp only [weightedBlock, smul_sub]
  exact Matrix.blockDiagonal_sub _ _
lemma hsSq_weightedBlock_sub (w : R → ℝ) (hw : ∀ r, 0 ≤ w r) (C D : R → Matrix m n ℂ) :
    hsSq (weightedBlock w C-weightedBlock w D) = ∑ r, w r*hsSq (C r-D r) := by
  rw [← weightedBlock_sub, hsSq_weightedBlock w hw]
variable {A : Type u_A} {B : Type u_B} [Fintype A] [Fintype B] [DecidableEq m] [DecidableEq n]
lemma payoff_weightedBlock (w : R → ℝ) (hw : ∀ r, 0 ≤ w r) (C : R → Matrix m n ℂ)
    (P : R → POVM m A) (Q : R → POVM n B) (V : A → B → Bool) :
    payoff (weightedBlock w C) (POVM.blocks P) (POVM.blocks Q) V =
      ∑ r, w r*payoff (C r) (P r) (Q r) V := by
  simp only [weightedBlock, payoff_blockDiagonal, payoff_smul, Real.sq_sqrt (hw _)]
end Stack

lemma correlated_sampling_value_rect {m n : Type} [Fintype m] [DecidableEq m] [Nonempty m]
    [Fintype n] [DecidableEq n] [Nonempty n]
    {x y a b : ℕ} (G : Game x y a b)
    (M : Fin (x+1) → Matrix m n ℂ) (N : Fin (y+1) → Matrix m n ℂ)
    (hM : ∀ x, hsSq (M x) = 1) (hN : ∀ y, hsSq (N y) = 1)
    (P : Fin (x+1) → POVM m (Fin (a+1))) (Q : Fin (y+1) → POVM n (Fin (b+1)))
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    (∑ z : Fin (x+1) × Fin (y+1), G.questionProb z *
      payoff (M z.1) (P z.1) (Q z.2) (G.accepts z.1 z.2)) ≤ entangledValue G +
      4*Real.sqrt (2*ε^2+(12/ε)*Real.sqrt (2*∑ z : Fin (x+1) × Fin (y+1),
        G.questionProb z * hsSq (M z.1-N z.2))) := by
  have hh := correlated_sampling_value G (fun x => squareState (M x)) (fun y => squareState (N y))
    (fun x => (hsSq_squareState _).trans (hM x)) (fun y => (hsSq_squareState _).trans (hN y))
    (fun x => (P x).sum (POVM.default 0)) (fun y => (POVM.default 0).sum (Q y)) hε hε1
  simpa only [payoff_squareState, ← squareState_sub, hsSq_squareState] using hh

lemma avg_payoff_difference_unbounded {Z : Type u_Z} {m : Type u_m} {n : Type u_n} {A : Type u_A} {B : Type u_B} [Fintype Z] [Fintype m] [Fintype n]
    [Fintype A] [Fintype B] [DecidableEq m] [DecidableEq n]
    (μ : Law Z) (C D : Z → Matrix m n ℂ) (hD : ∀ z, hsSq (D z) ≤ 1)
    (P : Z → POVM m A) (Q : Z → POVM n B) (V : Z → A → B → Bool) :
    μ.avg (fun z => payoff (C z) (P z) (Q z) (V z)) -
      μ.avg (fun z => payoff (D z) (P z) (Q z) (V z)) ≤
      2*Real.sqrt (μ.avg (fun z => hsSq (C z-D z))) + μ.avg (fun z => hsSq (C z-D z)) := by
  rw [← avg_sub]
  have he := μ.avg_mono (fun z => payoff_difference_unbounded (C z) (D z) (P z) (Q z) (V z) (hD z))
  apply he.trans
  rw [avg_add]
  apply add_le_add _ (le_refl _)
  rw [show (fun z => 2*Real.sqrt (hsSq (C z-D z))) = (fun z => (2:ℝ) • Real.sqrt (hsSq (C z-D z))) from rfl,
    avg_smul]
  exact mul_le_mul_of_nonneg_left (weighted_sqrt_le _ _ μ.nonneg (fun z => hsSq_nonneg _) μ.total) (by norm_num)
end ThresholdParallelRepetition.QuantumSampling

end

end OAI
