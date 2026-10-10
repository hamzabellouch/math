import OAI.Probability.EntangledGames.SamplingStrategy

namespace OAI

universe u_m u_n u_A u_B u_p u_ι

open scoped BigOperators ComplexOrder
open scoped MatrixOrder
open Matrix
open MeasureTheory Filter Set
open scoped Topology
open scoped Matrix.Norms.Elementwise
open scoped Interval
open scoped Kronecker

noncomputable section
open scoped BigOperators MatrixOrder ComplexOrder Kronecker
open Matrix
namespace ThresholdParallelRepetition.QuantumSampling
section Norm
open scoped Matrix.Norms.Frobenius
variable {m : Type u_m} {n : Type u_n} [Fintype m] [Fintype n]
lemma norm_eq_sqrt_hsSq (M : Matrix m n ℂ) : ‖M‖ = Real.sqrt (hsSq M) := by
  simp only [Matrix.frobenius_norm_def, Real.sqrt_eq_rpow, hsSq,
    Real.rpow_two, Complex.sq_norm]
lemma hsSq_le_one_norm {M : Matrix m n ℂ} (hM : hsSq M ≤ 1) : ‖M‖ ≤ 1 := by
  rw [norm_eq_sqrt_hsSq]
  exact Real.sqrt_le_one.mpr hM
lemma hsSq_difference_le (M N : Matrix m n ℂ) (hM : hsSq M ≤ 1) (hN : hsSq N ≤ 1) :
    hsSq M - hsSq N ≤ 2 * Real.sqrt (hsSq (M-N)) := by
  have hm := hsSq_le_one_norm hM
  have hn := hsSq_le_one_norm hN
  have hd := norm_sub_norm_le M N
  have h0 := norm_nonneg M
  have h1 := norm_nonneg N
  have h2 := norm_nonneg (M-N)
  have hh := mul_le_mul_of_nonneg_left hd (add_nonneg h0 h1)
  have hh' := mul_le_mul_of_nonneg_right (add_le_add hm hn) h2
  rw [norm_eq_sqrt_hsSq M, norm_eq_sqrt_hsSq N, norm_eq_sqrt_hsSq (M-N)] at hh hh'
  have hsqM := Real.sq_sqrt (hsSq_nonneg M)
  have hsqN := Real.sq_sqrt (hsSq_nonneg N)
  nlinarith
end Norm

section WinEffect
variable {m : Type u_m} {n : Type u_n} {A : Type u_A} {B : Type u_B} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    [Fintype A] [Fintype B]
def winEffect (P : POVM m A) (Q : POVM n B) (V : A → B → Bool) :
    Matrix (m × n) (m × n) ℂ := ∑ a, ∑ b, if V a b then P.effect a ⊗ₖ Q.effect b else 0
lemma winEffect_pos (P : POVM m A) (Q : POVM n B) (V : A → B → Bool) :
    (winEffect P Q V).PosSemidef := by
  apply Matrix.posSemidef_sum; intro a _
  apply Matrix.posSemidef_sum; intro b _
  split
  · exact (P.pos a).kronecker (Q.pos b)
  · exact Matrix.PosSemidef.zero
lemma winEffect_le_one (P : POVM m A) (Q : POVM n B) (V : A → B → Bool) :
    winEffect P Q V ≤ 1 := by
  have hsum : (∑ a, ∑ b, P.effect a ⊗ₖ Q.effect b) = (1 : Matrix (m × n) (m × n) ℂ) := by
    simp only [← kronecker_sum_right, ← kronecker_sum_left, P.total, Q.total,
      Matrix.one_kronecker_one]
  rw [← hsum]
  apply Finset.sum_le_sum; intro a _
  apply Finset.sum_le_sum; intro b _
  split
  · exact le_rfl
  · exact ((P.pos a).kronecker (Q.pos b)).nonneg

def flat (C : Matrix m n ℂ) : Matrix (m × n) Unit ℂ := Matrix.replicateCol Unit (vec C)
omit [DecidableEq m] [DecidableEq n] in
lemma hsSq_flat (C : Matrix m n ℂ) : hsSq (flat C) = hsSq C := by
  simp [hsSq, flat, vec, Fintype.sum_prod_type]
omit [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] in
lemma flat_sub (C D : Matrix m n ℂ) : flat (C-D) = flat C-flat D := rfl
omit [DecidableEq m] [DecidableEq n] in
lemma flat_form (C : Matrix m n ℂ) (W : Matrix (m × n) (m × n) ℂ) :
    Matrix.trace ((flat C)ᴴ*(W*flat C)) = star (vec C) ⬝ᵥ (W *ᵥ vec C) := by
  simp only [Matrix.trace, Matrix.diag, Fintype.sum_unique, Matrix.mul_apply,
    Matrix.conjTranspose_apply, flat, Matrix.replicateCol_apply, dotProduct,
    Matrix.mulVec, Pi.star_apply]
lemma payoff_eq_form (C : Matrix m n ℂ) (P : POVM m A) (Q : POVM n B)
    (V : A → B → Bool) :
    payoff C P Q V = (star (vec C) ⬝ᵥ (winEffect P Q V *ᵥ vec C)).re := by
  simp only [winEffect, Matrix.sum_mulVec, dotProduct_sum, Complex.re_sum, payoff]
  apply Finset.sum_congr rfl; intro a _
  apply Finset.sum_congr rfl; intro b _
  split
  · rfl
  · simp only [Matrix.zero_mulVec, dotProduct_zero, Complex.zero_re]
lemma payoff_eq_hsSq (C : Matrix m n ℂ) (P : POVM m A) (Q : POVM n B)
    (V : A → B → Bool) :
    payoff C P Q V = hsSq (CFC.sqrt (winEffect P Q V) * flat C) := by
  rw [hsSq_eq_trace, Matrix.conjTranspose_mul]
  have hh : (CFC.sqrt (winEffect P Q V)).IsHermitian :=
    (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg _)).isHermitian
  rw [hh.eq, Matrix.mul_assoc, ← Matrix.mul_assoc (CFC.sqrt _) (CFC.sqrt _),
    CFC.sqrt_mul_sqrt_self _ (winEffect_pos P Q V).nonneg, flat_form, payoff_eq_form]
lemma winSqrt_contraction (P : POVM m A) (Q : POVM n B) (V : A → B → Bool) :
    (CFC.sqrt (winEffect P Q V))ᴴ*CFC.sqrt (winEffect P Q V) ≤ 1 := by
  have hh : (CFC.sqrt (winEffect P Q V)).IsHermitian :=
    (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg _)).isHermitian
  rw [hh.eq, CFC.sqrt_mul_sqrt_self _ (winEffect_pos P Q V).nonneg]
  exact winEffect_le_one P Q V
lemma payoff_difference_le (C D : Matrix m n ℂ) (P : POVM m A) (Q : POVM n B)
    (V : A → B → Bool) (hC : hsSq C ≤ 1) (hD : hsSq D ≤ 1) :
    payoff C P Q V - payoff D P Q V ≤ 2*Real.sqrt (hsSq (C-D)) := by
  have hsc := (hsSq_mul_contraction (winSqrt_contraction P Q V) (flat C)).trans
    (le_trans (le_of_eq (hsSq_flat C)) hC)
  have hsd := (hsSq_mul_contraction (winSqrt_contraction P Q V) (flat D)).trans
    (le_trans (le_of_eq (hsSq_flat D)) hD)
  rw [payoff_eq_hsSq, payoff_eq_hsSq]
  refine (hsSq_difference_le _ _ hsc hsd).trans ?_
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply Real.sqrt_le_sqrt
  rw [← Matrix.mul_sub, ← flat_sub]
  exact (hsSq_mul_contraction (winSqrt_contraction P Q V) _).trans_eq (hsSq_flat _)
end WinEffect

lemma payoff_ratio_loss {w q a b c e : ℝ} (_he : 0 ≤ e) (hq : 0 ≤ q) (hqc : q ≤ c)
    (hca : c ≤ a) (hcb : c ≤ b) (ha : a ≤ 1) (hb : b ≤ 1)
    (hwq : w-q ≤ 2*Real.sqrt e) (hc : 1-c ≤ 2*Real.sqrt e) :
    w ≤ q/(a+b-c) + 4*Real.sqrt e := by
  have hc0 : 0 ≤ c := hq.trans hqc
  have hd0 : 0 ≤ a+b-c := by linarith
  by_cases hd : a+b-c = 0
  · have hq0 : q = 0 := by linarith
    rw [hq0, zero_div]
    rw [hq0, sub_zero] at hwq
    linarith [Real.sqrt_nonneg e]
  · have hdpos : 0 < a+b-c := lt_of_le_of_ne hd0 (Ne.symm hd)
    have hr0 : 0 ≤ q/(a+b-c) := div_nonneg hq hd0
    have hr1 : q/(a+b-c) ≤ 1 := (div_le_one hdpos).mpr (by linarith)
    have hde : a+b-c ≤ 1+2*Real.sqrt e := by linarith
    have hm := mul_le_mul_of_nonneg_left hde hr0
    have hprod : q/(a+b-c)*(a+b-c) = q := div_mul_cancel₀ q hd
    rw [hprod] at hm
    have he' := Real.sqrt_nonneg e
    nlinarith

theorem filter_approximation_value {m n p q : Type} [Fintype m] [Fintype n]
    [Fintype p] [Fintype q] [DecidableEq m] [DecidableEq n] [DecidableEq p] [DecidableEq q]
    [Nonempty n] [Nonempty q] {x y a b : ℕ} (G : Game x y a b)
    (D : Matrix n q ℂ) (hD : 0 < hsSq D)
    (M : Fin (x+1) → Matrix m p ℂ) (hM : ∀ x, hsSq (M x) = 1)
    (P : Fin (x+1) → POVM m (Fin (a+1))) (Q : Fin (y+1) → POVM p (Fin (b+1)))
    (K : Fin (x+1) → Matrix m n ℂ) (L : Fin (y+1) → Matrix p q ℂ)
    (hK : ∀ x, (K x)ᴴ*K x ≤ 1) (hL : ∀ y, (L y)ᴴ*L y ≤ 1)
    (hA : ∀ x, hsSq (K x*D) ≤ 1) (hB : ∀ y, hsSq (D*(L y)ᵀ) ≤ 1) :
    (∑ z : Fin (x+1) × Fin (y+1), G.questionProb z *
        payoff (M z.1) (P z.1) (Q z.2) (G.accepts z.1 z.2)) ≤ entangledValue G +
      4*Real.sqrt (∑ z : Fin (x+1) × Fin (y+1), G.questionProb z *
        hsSq (M z.1 - K z.1*D*(L z.2)ᵀ)) := by
  have hv := finite_filter_value_unnormalized G D hD P Q K L hK hL
  have hp : ∀ z : Fin (x+1) × Fin (y+1),
      payoff (M z.1) (P z.1) (Q z.2) (G.accepts z.1 z.2) ≤
        payoff (K z.1*D*(L z.2)ᵀ) (P z.1) (Q z.2) (G.accepts z.1 z.2) /
          (hsSq (K z.1*D)+hsSq (D*(L z.2)ᵀ)-hsSq (K z.1*D*(L z.2)ᵀ)) +
          4*Real.sqrt (hsSq (M z.1-K z.1*D*(L z.2)ᵀ)) := by
    intro z
    obtain ⟨hca,hcb,_,_⟩ := filter_mass_bounds D (K z.1) (L z.2) (hK z.1) (hL z.2)
    apply payoff_ratio_loss (hsSq_nonneg _) (payoff_nonneg _ _ _ _) (payoff_le_hsSq _ _ _ _)
      hca hcb (hA z.1) (hB z.2)
    · exact payoff_difference_le _ _ _ _ _ (le_of_eq (hM z.1)) (hca.trans (hA z.1))
    · simpa only [hM z.1] using
        hsSq_difference_le (M z.1) (K z.1*D*(L z.2)ᵀ) (le_of_eq (hM z.1)) (hca.trans (hA z.1))
  have hh := Finset.sum_le_sum (s := Finset.univ) (fun z _ =>
    mul_le_mul_of_nonneg_left (hp z) (G.questionProb_nonneg z))
  simp only [mul_add, Finset.sum_add_distrib] at hh
  have hroot := weighted_sqrt_le G.questionProb
    (fun z => hsSq (M z.1-K z.1*D*(L z.2)ᵀ)) G.questionProb_nonneg
    (fun _ => hsSq_nonneg _) G.questionProb_sum
  have hfour : (∑ z : Fin (x+1) × Fin (y+1), G.questionProb z *
      (4*Real.sqrt (hsSq (M z.1-K z.1*D*(L z.2)ᵀ)))) =
      4*∑ z : Fin (x+1) × Fin (y+1), G.questionProb z *
        Real.sqrt (hsSq (M z.1-K z.1*D*(L z.2)ᵀ)) := by
    rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro z _; ring
  rw [hfour] at hh
  linarith

section Blocks
variable {m : Type u_m} {n : Type u_n} {p : Type u_p} {ι : Type u_ι} [Fintype m] [Fintype n] [Fintype p] [Fintype ι]
def rowBlocks (F : ι → Matrix m n ℂ) : Matrix m (n × ι) ℂ := fun i j => F j.2 i j.1
omit [Fintype m] [Fintype n] [Fintype p] in
lemma rowBlocks_mul_transpose (F : ι → Matrix m n ℂ) (G : ι → Matrix p n ℂ) [Fintype n] :
    rowBlocks F * (rowBlocks G)ᵀ = ∑ l, F l*(G l)ᵀ := by
  ext i j
  simp only [Matrix.mul_apply, rowBlocks, Matrix.transpose_apply, Fintype.sum_prod_type,
    Matrix.sum_apply]
  rw [Finset.sum_comm]
omit [Fintype m] [Fintype p] in
lemma rowBlocks_mul_diagonal [DecidableEq n] [DecidableEq ι]
    (F : ι → Matrix m n ℂ) (r : ι → ℝ) :
    rowBlocks F * Matrix.diagonal (fun j : n × ι => (r j.2 : ℂ)) =
      rowBlocks (fun l => r l • F l) := by
  ext i j
  simp only [Matrix.mul_diagonal, rowBlocks, Matrix.smul_apply, Complex.real_smul]
  ring
omit [Fintype p] in
lemma hsSq_rowBlocks (F : ι → Matrix m n ℂ) :
    hsSq (rowBlocks F) = ∑ l, hsSq (F l) := by
  simp only [hsSq, rowBlocks, Fintype.sum_prod_type]
  conv_lhs => arg 2; ext i; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
omit [Fintype p] [Fintype ι] in
lemma hsSq_transpose (C : Matrix m n ℂ) : hsSq Cᵀ = hsSq C := by
  simp only [hsSq, Matrix.transpose_apply]
  exact Finset.sum_comm
omit [Fintype m] [Fintype p] [Fintype ι] in
lemma projectionRows_gram [DecidableEq ι] (P : ι → Matrix n n ℂ)
    (hP : ∀ l, (P l).IsHermitian) (hPP : ∀ l, P l*P l = P l)
    (horth : ∀ l t, l ≠ t → P l*P t = 0) :
    (rowBlocks P)ᴴ*rowBlocks P = Matrix.blockDiagonal P := by
  ext ⟨i,l⟩ ⟨j,t⟩
  change ((P l)ᴴ*P t) i j = _
  rw [(hP l).eq]
  by_cases hlt : l = t
  · subst t
    rw [hPP l, Matrix.blockDiagonal_apply_eq]
  · rw [horth l t hlt]
    simp only [Matrix.zero_apply, Matrix.blockDiagonal_apply, ite_eq_right hlt]
omit [Fintype m] [Fintype p] in
lemma projectionRows_contraction [DecidableEq n] [DecidableEq ι] (P : ι → Matrix n n ℂ)
    (hP : ∀ l, (P l).IsHermitian) (hPP : ∀ l, P l*P l = P l)
    (horth : ∀ l t, l ≠ t → P l*P t = 0) : (rowBlocks P)ᴴ*rowBlocks P ≤ 1 := by
  rw [projectionRows_gram P hP hPP horth]
  apply projection_le_one
  · change (Matrix.blockDiagonal P)ᴴ = _
    rw [Matrix.blockDiagonal_conjTranspose]
    congr 1; funext l; exact (hP l).eq
  · rw [← Matrix.blockDiagonal_mul]
    congr 1; funext l; exact hPP l
end Blocks

section Resource
variable {n : Type u_n} [Fintype n] [DecidableEq n]
def binResource (L : Finset ℤ) (ε s : ℝ) : Matrix (n × L) (n × L) ℂ :=
  Matrix.diagonal (fun j => (binScale ε s j.2 : ℂ))
def bobBinFilter (L : Finset ℤ) (N : Matrix n n ℂ) (ε s : ℝ) : Matrix n (n × L) ℂ :=
  rowBlocks (fun l : L => (binProjection (rightAbs N) ε s l)ᵀ)
lemma bobBinFilter_contraction (L : Finset ℤ) (N : Matrix n n ℂ) (ε s : ℝ) :
    (bobBinFilter L N ε s)ᴴ*bobBinFilter L N ε s ≤ 1 := by
  apply projectionRows_contraction
  · intro l; exact (binProjection_hermitian _ _ _ _).transpose
  · intro l
    rw [← Matrix.transpose_mul, binProjection_sq (rightAbs_pos N).isHermitian]
  · intro l t hlt
    rw [← Matrix.transpose_mul,
      binProjection_orthogonal (rightAbs_pos N).isHermitian ε s (Subtype.coe_ne_coe.mpr (Ne.symm hlt)),
      Matrix.transpose_zero]
omit [Fintype n] in
lemma binResource_transpose (L : Finset ℤ) (ε s : ℝ) :
    (binResource (n := n) L ε s)ᵀ = binResource (n := n) L ε s := Matrix.diagonal_transpose _
lemma binResource_pos [Nonempty n] (L : Finset ℤ) [Nonempty L] (ε s : ℝ) :
    0 < hsSq (binResource (n := n) L ε s) := by
  simp only [hsSq, binResource, Matrix.diagonal_apply, apply_ite Complex.normSq,
    Complex.normSq_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true, Complex.normSq_ofReal]
  apply Finset.sum_pos'
  · intro i _; exact mul_self_nonneg _
  · exact ⟨(Classical.choice ‹Nonempty n›, Classical.choice ‹Nonempty L›), Finset.mem_univ _,
      mul_pos (Real.exp_pos _) (Real.exp_pos _)⟩
lemma bin_output (L : Finset ℤ) (M N : Matrix n n ℂ) (ε s : ℝ) :
    binFilter L M ε s * binResource (n := n) L ε s * (bobBinFilter L N ε s)ᵀ =
      polar M*crossBins L (rightAbs M) (rightAbs N) ε s := by
  change rowBlocks (fun l : L => polar M*binProjection (rightAbs M) ε s l) *
    Matrix.diagonal (fun j : n × L => (binScale ε s j.2 : ℂ)) *
    (rowBlocks (fun l : L => (binProjection (rightAbs N) ε s l)ᵀ))ᵀ = _
  rw [rowBlocks_mul_diagonal _ (fun l : L => binScale ε s l), rowBlocks_mul_transpose]
  simp only [Matrix.transpose_transpose, Matrix.smul_mul, crossBins, Matrix.mul_sum,
    Matrix.mul_smul, Matrix.mul_assoc]
lemma hsSq_polar_bin (M : Matrix n n ℂ) (ε s : ℝ) (l : ℤ) :
    hsSq (polar M*binProjection (rightAbs M) ε s l) =
      hsSq (binProjection (rightAbs M) ε s l) := by
  rw [hsSq_eq_trace, hsSq_eq_trace, Matrix.conjTranspose_mul]
  rw [Matrix.mul_assoc, ← Matrix.mul_assoc (polar M)ᴴ (polar M), polar_gram_bin]
lemma hsSq_roundedAbs_eq_sum (L : Finset ℤ) {A : Matrix n n ℂ} (hA : A.IsHermitian)
    (ε s : ℝ) (hL : CoversBins L A ε s) :
    hsSq (roundedAbs A ε s) = ∑ l : L, (binScale ε s l)^2*hsSq (binProjection A ε s l) := by
  rw [roundedAbs_eq_sum L ε s hL, hsSq_sum_orthogonal]
  · simp only [hsSq_smul]
  · intro l t hlt
    simp only [Matrix.conjTranspose_smul, star_trivial, Matrix.smul_mul, Matrix.mul_smul,
      (binProjection_hermitian A ε s l).eq]
    rw [binProjection_orthogonal hA ε s (Subtype.coe_ne_coe.mpr hlt), smul_zero, smul_zero]
lemma bin_left_mass (L : Finset ℤ) (M : Matrix n n ℂ) (ε s : ℝ)
    (hL : CoversBins L (rightAbs M) ε s) :
    hsSq (binFilter L M ε s*binResource (n := n) L ε s) = hsSq (roundedAbs (rightAbs M) ε s) := by
  change hsSq (rowBlocks (fun l : L => polar M*binProjection (rightAbs M) ε s l) *
    Matrix.diagonal (fun j : n × L => (binScale ε s j.2 : ℂ))) = _
  rw [rowBlocks_mul_diagonal _ (fun l : L => binScale ε s l), hsSq_rowBlocks, hsSq_roundedAbs_eq_sum L (rightAbs_pos M).isHermitian ε s hL]
  simp only [hsSq_smul, hsSq_polar_bin]
lemma bin_right_mass (L : Finset ℤ) (N : Matrix n n ℂ) (ε s : ℝ)
    (hL : CoversBins L (rightAbs N) ε s) :
    hsSq (binResource (n := n) L ε s*(bobBinFilter L N ε s)ᵀ) = hsSq (roundedAbs (rightAbs N) ε s) := by
  rw [← hsSq_transpose, Matrix.transpose_mul, Matrix.transpose_transpose, binResource_transpose]
  change hsSq (rowBlocks (fun l : L => (binProjection (rightAbs N) ε s l)ᵀ) *
    Matrix.diagonal (fun j : n × L => (binScale ε s j.2 : ℂ))) = _
  rw [rowBlocks_mul_diagonal _ (fun l : L => binScale ε s l), hsSq_rowBlocks, hsSq_roundedAbs_eq_sum L (rightAbs_pos N).isHermitian ε s hL]
  simp only [hsSq_smul, hsSq_transpose]
end Resource

theorem correlated_sampling_value {n : Type} [Fintype n] [DecidableEq n] [Nonempty n]
    {x y a b : ℕ} (G : Game x y a b)
    (M : Fin (x+1) → Matrix n n ℂ) (N : Fin (y+1) → Matrix n n ℂ)
    (hM : ∀ x, hsSq (M x) = 1) (hN : ∀ y, hsSq (N y) = 1)
    (P : Fin (x+1) → POVM n (Fin (a+1))) (Q : Fin (y+1) → POVM n (Fin (b+1)))
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    (∑ z : Fin (x+1) × Fin (y+1), G.questionProb z *
      payoff (M z.1) (P z.1) (Q z.2) (G.accepts z.1 z.2)) ≤ entangledValue G +
      4*Real.sqrt (2*ε^2+(12/ε)*Real.sqrt (2*∑ z : Fin (x+1) × Fin (y+1),
        G.questionProb z * hsSq (M z.1-N z.2))) := by
  have hMA : ∀ x, hsSq (rightAbs (M x)) = 1 := fun x => (hsSq_sqrt_gram (M x)).trans (hM x)
  have hNA : ∀ y, hsSq (rightAbs (N y)) = 1 := fun y => (hsSq_sqrt_gram (N y)).trans (hN y)
  obtain ⟨s,hs⟩ := exists_shift_spectralEnvelope_le G.questionProb G.questionProb_nonneg
    G.questionProb_sum (fun z => rightAbs (M z.1)) (fun z => rightAbs (N z.2))
    (fun z => rightAbs_pos (M z.1)) (fun z => rightAbs_pos (N z.2))
    (fun z => hMA z.1) (fun z => hNA z.2) hε hε1
  obtain ⟨L,hL0,hL⟩ := exists_common_bins
    (Sum.elim (fun x => rightAbs (M x)) (fun y => rightAbs (N y))) ε s
  let : Nonempty L := ⟨⟨0,hL0⟩⟩
  have hLM : ∀ x, CoversBins L (rightAbs (M x)) ε s := fun x => hL (Sum.inl x)
  have hLN : ∀ y, CoversBins L (rightAbs (N y)) ε s := fun y => hL (Sum.inr y)
  have hleft : ∀ x, hsSq (binFilter L (M x) ε s*binResource (n := n) L ε s) ≤ 1 := by
    intro x
    rw [bin_left_mass L (M x) ε s (hLM x)]
    exact (roundedAbs_energy_le (rightAbs_pos (M x)) hε s).trans_eq (hMA x)
  have hright : ∀ y, hsSq (binResource (n := n) L ε s*(bobBinFilter L (N y) ε s)ᵀ) ≤ 1 := by
    intro y
    rw [bin_right_mass L (N y) ε s (hLN y)]
    exact (roundedAbs_energy_le (rightAbs_pos (N y)) hε s).trans_eq (hNA y)
  have hv := filter_approximation_value G (binResource (n := n) L ε s) (binResource_pos L ε s)
    M hM P Q (fun x => binFilter L (M x) ε s) (fun y => bobBinFilter L (N y) ε s)
    (fun x => binFilter_contraction L (M x) ε s)
    (fun y => bobBinFilter_contraction L (N y) ε s) hleft hright
  apply hv.trans
  apply add_le_add_right
  apply mul_le_mul_of_nonneg_left _ (show (0 : ℝ) ≤ 4 by norm_num)
  apply Real.sqrt_le_sqrt
  simp only [bin_output]
  have he : ∀ z : Fin (x+1) × Fin (y+1),
      hsSq (M z.1-polar (M z.1)*crossBins L (rightAbs (M z.1)) (rightAbs (N z.2)) ε s) ≤
      2*ε^2 + 2*spectralEnvelope (rightAbs_pos (M z.1)).isHermitian
        (rightAbs_pos (N z.2)).isHermitian ε s := by
    intro z
    have herr := polar_crossBins_error_le L (M z.1) (N z.2) hε s (hLM z.1)
    rw [hM z.1, mul_one] at herr
    have hmis := binProjection_mismatch_le L (rightAbs_pos (M z.1)) (rightAbs_pos (N z.2)) hε s
    rw [← Finset.sum_coe_sort L] at hmis
    change binMismatch L _ _ ε s ≤ _ at hmis
    linarith
  have hsum := Finset.sum_le_sum (s := Finset.univ)
    (fun z _ => mul_le_mul_of_nonneg_left (he z) (G.questionProb_nonneg z))
  have heq : (∑ z : Fin (x+1) × Fin (y+1), G.questionProb z *
      (2*ε^2+2*spectralEnvelope (rightAbs_pos (M z.1)).isHermitian
        (rightAbs_pos (N z.2)).isHermitian ε s)) =
      2*ε^2 + 2*∑ z : Fin (x+1) × Fin (y+1), G.questionProb z *
        spectralEnvelope (rightAbs_pos (M z.1)).isHermitian
          (rightAbs_pos (N z.2)).isHermitian ε s := by
    simp only [mul_add, Finset.sum_add_distrib]
    rw [← Finset.sum_mul, G.questionProb_sum, one_mul, Finset.mul_sum]
    congr 1; apply Finset.sum_congr rfl; intro z _; ring
  rw [heq] at hsum
  have habs : (∑ z : Fin (x+1) × Fin (y+1), G.questionProb z *
      hsSq (rightAbs (M z.1)-rightAbs (N z.2))) ≤
      2*∑ z : Fin (x+1) × Fin (y+1), G.questionProb z * hsSq (M z.1-N z.2) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum; intro z _
    have hh := mul_le_mul_of_nonneg_left (hsSq_right_absolute_sub_le (M z.1) (N z.2))
      (G.questionProb_nonneg z)
    dsimp [rightAbs]
    convert hh using 1
    ring
  have hh := mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt habs) (show 0 ≤ 6/ε by positivity)
  have hh' := hs.trans hh
  calc
    _ ≤ 2*ε^2 + 2*((6/ε)*Real.sqrt (2*∑ z : Fin (x+1) × Fin (y+1),
        G.questionProb z * hsSq (M z.1-N z.2))) :=
      hsum.trans (add_le_add_right (mul_le_mul_of_nonneg_left hh' (by norm_num)) _)
    _ = _ := by ring
end ThresholdParallelRepetition.QuantumSampling

end

end OAI
