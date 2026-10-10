import Mathlib
import OAI.Probability.SKGap.Matrix.ConditionalMiddleNorm
import OAI.Probability.SKGap.Localization.ConditionalMiddleSize

namespace OAI

section
noncomputable section
namespace SKGap
open Matrix Real Set MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix.Norms.Frobenius

lemma outer_symmetric {ι : Type*} (x : ι → ℝ) : (vecMulVec x x).IsHermitian := by
  ext i k
  simp only [conjTranspose_apply,star_trivial,vecMulVec_apply]
  ring

lemma outer_sum_symmetric {ι : Type*} (x y : ι → ℝ) : (vecMulVec x y+vecMulVec y x).IsHermitian := by
  ext i k
  simp only [conjTranspose_apply,star_trivial,Matrix.add_apply,vecMulVec_apply]
  ring

lemma conditionalBlockMatrix_hermitian {ι : Type*} [Fintype ι] [DecidableEq ι]
    (r j q s S a B κ ell : ℝ) (u Z : ι → ℝ) (g : MatrixCoordinates ι → ℝ) :
    (conditionalBlockMatrix r j q s S a B κ ell u Z g).IsHermitian := by
  unfold conditionalBlockMatrix
  rw [goeBlockResidual_expand]
  have hh := (goeMatrix_symm r g).add ((outer_sum_symmetric u (goeMatrix r g*ᵥu)).smul
    (R := ℝ) (isSelfAdjoint_iff.mpr (star_trivial (κ-1))))
  have hh' := hh.add ((outer_symmetric u).smul (R := ℝ)
    (isSelfAdjoint_iff.mpr (star_trivial ((ell-2*κ+1)*goeBilinear r u u g))))
  convert (hh'.add (outer_sum_symmetric u ((j*sqrt (q/s)) • Z-(j*a/s) • u))).add
    ((outer_symmetric u).smul (R := ℝ) (isSelfAdjoint_iff.mpr (star_trivial (2*j*(a+B*q)/S)))) using 1
  congr 1
  abel

lemma empiricalConditionalMiddle_hermitian {n : ℕ} [NeZero n] (j t σ : ℝ)
    (y : Fin n → ℝ) (g : MatrixCoordinates (Fin n) → ℝ) :
    (empiricalConditionalMiddle j t σ y g).IsHermitian := by
  unfold empiricalConditionalMiddle
  exact (((conditionalBlockMatrix_hermitian _ _ _ _ _ _ _ _ _ _ _ _).add
    ((outer_symmetric _).smul (R := ℝ) (isSelfAdjoint_iff.mpr (star_trivial _)))).add
    ((outer_symmetric _).smul (R := ℝ) (isSelfAdjoint_iff.mpr (star_trivial _)))).sub
    (Matrix.isHermitian_one.smul (R := ℝ) (isSelfAdjoint_iff.mpr (star_trivial _)))

lemma empiricalConditionalMiddle_norm {n : ℕ} [NeZero n] (j t σ : ℝ)
    (y : Fin n → ℝ) {V W : ℝ} (hV : 0 ≤ V)
    (g : MatrixCoordinates (Fin n) → ℝ)
    (hq : 0 < scalarQMoment (empiricalLaw y))
    (hcols : ∀ k, ‖empiricalGramColumns y (scalarD j (empiricalLaw y,t,σ))
      (scalarS j (empiricalLaw y,t,σ)) k‖ ≤ V)
    (hW : opNorm (goeMatrix (j/(n:ℝ)) g) ≤ W) :
    opNorm (empiricalConditionalMiddle j t σ y g) ≤
      conditionalMiddleSize j V W (empiricalLaw y,t,σ) := by
  let p : ScalarPoint := (empiricalLaw y,t,σ)
  let q := scalarQMoment p.1
  let s := scalarS j p
  let B := j*scalarBMoment p.1
  let u := empiricalUnit y q
  let X := empiricalGramColumns y (scalarD j p) s 0
  let Z := sqrt s • empiricalGramColumns y (scalarD j p) s 2
  have hu : ‖u‖=1 := empiricalUnit_norm y hq
  have hZ : ‖Z‖ ≤ sqrt s*V := by
    dsimp [Z]
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (sqrt_nonneg _)]
    exact mul_le_mul_of_nonneg_left (hcols 2) (sqrt_nonneg _)
  have hX : opNorm (vecMulVec X.ofLp X.ofLp) ≤ V^2 := by
    apply (operator_vecMulVec_le X X).trans
    simpa only [pow_two] using mul_le_mul (hcols 0) (hcols 0) (norm_nonneg _) hV
  have hu' : opNorm (vecMulVec u.ofLp u.ofLp) ≤ 1 := by
    simpa only [hu,mul_one] using operator_vecMulVec_le u u
  have hI : opNorm (1 : Matrix (Fin n) (Fin n) ℝ) ≤ 1 := by
    simpa only [Matrix.diagonal_one] using opNorm_diagonal_le (ι := Fin n) zero_le_one (d := fun _=>1)
      (fun _=>by norm_num)
  have hb := conditionalBlockMatrix_norm (r := j/(n:ℝ)) (j := j) (q := q) (s := s)
    (S := s+j*q) (a := scalarA j p) (B := B) (κ := conditionalKappa j p)
    (ell := conditionalEll j p) u Z g hu
  have hc : opNorm (conditionalBlockMatrix (j/(n:ℝ)) j q s (s+j*q) (scalarA j p) B
      (conditionalKappa j p) (conditionalEll j p) u.ofLp Z.ofLp g) ≤
      (1+2*|conditionalKappa j p-1|+|conditionalEll j p-2*conditionalKappa j p+1|)*W+
      2*(|j*sqrt (q/s)| * (sqrt s*V)+|j*scalarA j p/s|)+|2*j*(scalarA j p+B*q)/(s+j*q)| := by
    apply hb.trans
    have hn := mul_le_mul_of_nonneg_left hW (by positivity : 0 ≤ 1+2*|conditionalKappa j p-1|+|conditionalEll j p-2*conditionalKappa j p+1|)
    have hz := mul_le_mul_of_nonneg_left hZ (abs_nonneg (j*sqrt (q/s)))
    linarith
  change opNorm (_+j • vecMulVec X.ofLp X.ofLp+(2*j*q) • vecMulVec u.ofLp u.ofLp-B • 1) ≤ _
  rw [sub_eq_add_neg,← neg_smul]
  apply (real_opNorm_add _ _).trans
  have h1 := real_opNorm_add (conditionalBlockMatrix (j/(n:ℝ)) j q s (s+j*q) (scalarA j p) B
      (conditionalKappa j p) (conditionalEll j p) u.ofLp Z.ofLp g+j • vecMulVec X.ofLp X.ofLp)
    ((2*j*q) • vecMulVec u.ofLp u.ofLp)
  have h2 := real_opNorm_add (conditionalBlockMatrix (j/(n:ℝ)) j q s (s+j*q) (scalarA j p) B
      (conditionalKappa j p) (conditionalEll j p) u.ofLp Z.ofLp g)
    (j • vecMulVec X.ofLp X.ofLp)
  rw [real_opNorm_smul] at h1 h2
  rw [real_opNorm_smul,abs_neg]
  have h3 := mul_le_mul_of_nonneg_left hX (abs_nonneg j)
  have h4 := mul_le_mul_of_nonneg_left hu' (abs_nonneg (2*j*q))
  have h5 := mul_le_mul_of_nonneg_left hI (abs_nonneg B)
  dsimp [conditionalMiddleSize,p,q,s,B,u,X,Z] at hc h1 h2 h3 h4 h5 ⊢
  nlinarith only [hc,h1,h2,h3,h4,h5]
end SKGap
end
end

section
noncomputable section
namespace SKGap
open Matrix Real Set MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix.Norms.Frobenius

lemma scalarS_pos_of_time {j t σ : ℝ} (hj : 0 ≤ j) (ht : 0 < t) (P : ProbabilityMeasure ℝ) :
    0 < scalarS j (P,t,σ) :=
  add_pos_of_pos_of_nonneg (add_pos_of_pos_of_nonneg ht (sq_nonneg _))
    (mul_nonneg hj (scalarQMoment_bounds _).1)

theorem empiricalConditionalMiddle_uniform_norm {j R t0 T : ℝ}
    (hj : 0 ≤ j) (hR : 0 ≤ R) (ht0 : 0 < t0) (W : ℝ) :
    ∃ L : ℝ, 1 ≤ L ∧ ∀ (n : ℕ) [NeZero n] (y : Fin n → ℝ),
      empiricalLaw y ∈ momentBall R → 0 < scalarQMoment (empiricalLaw y) →
      ∀ t ∈ Icc t0 T,∀ σ : ℝ, |σ| ≤ 1 →
      ∀ g : MatrixCoordinates (Fin n) → ℝ, opNorm (goeMatrix (j/(n:ℝ)) g) ≤ W →
      opNorm (empiricalConditionalMiddle j t σ y g) ≤ L := by
  let K := max 1 ((1+|T|+j)/t0)
  have hK : 1 ≤ K := le_max_left _ _
  let V := 2*K*(R+2)
  have hV : 0 ≤ V := by dsimp [V]; positivity
  obtain ⟨L,hL,hbd⟩ := conditionalMiddleSize_uniform (T := T) hj hR ht0 V W
  refine ⟨L,hL,?_⟩
  intro n _ y hy hq t ht σ hσ g hg
  have hs := scalarS_pos_of_time (σ := σ) hj (ht0.trans_le ht.1) (empiricalLaw y)
  have hcol : ∀ k,‖empiricalGramColumns y (scalarD j (empiricalLaw y,t,σ))
      (scalarS j (empiricalLaw y,t,σ)) k‖ ≤ V := by
    intro k
    convert empiricalGramColumns_norm (NeZero.pos n) y hs hK (by linarith : 0 ≤ R+1)
      (empirical_column_coefficient hj ht0 ht y) (empirical_moment_vector_bound hR y hy) k using 1
    dsimp [V]; ring
  exact (empiricalConditionalMiddle_norm j t σ y hV g hq hcol hg).trans (hbd _ hy t ht σ hσ)
end SKGap
end
end

end OAI
