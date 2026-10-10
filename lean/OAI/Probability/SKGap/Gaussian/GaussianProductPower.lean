import Mathlib
import OAI.Probability.SKGap.Gaussian.GaussianProductIntegral
import OAI.Probability.SKGap.Matrix.MatrixSeminorm

namespace OAI

section
noncomputable section
namespace SKGap
open Real MeasureTheory ProbabilityTheory
open scoped BigOperators
variable {κ : Type*} [Fintype κ]

lemma gaussianProduct_integrable_exp_lipschitz {F : EuclideanSpace ℝ κ→ℝ}
    {L : NNReal} (hF : LipschitzWith L F) (r : ℝ) :
    Integrable (fun g : κ→ℝ=>exp (r*F (WithLp.toLp 2 g))) (Measure.pi (fun _=>gaussianReal 0 1)) := by
  have hi := gaussian_integrable_exp_lipschitz (μ:=stdGaussian (EuclideanSpace ℝ κ)) hF r
  rw [←map_pi_eq_stdGaussian] at hi
  exact hi.comp_measurable (by fun_prop)

lemma gaussianProduct_integrable_abs_pow_lipschitz {F : EuclideanSpace ℝ κ→ℝ}
    {L : NNReal} (hF : LipschitzWith L F) (k : ℕ) :
    Integrable (fun g : κ→ℝ=>|F (WithLp.toLp 2 g)|^k) (Measure.pi (fun _=>gaussianReal 0 1)) := by
  let μ := Measure.pi (fun _ : κ=>gaussianReal 0 1)
  have h1 := gaussianProduct_integrable_exp_lipschitz hF 1
  have h2 := gaussianProduct_integrable_exp_lipschitz hF (-1)
  have hh := (h1.add h2).const_mul (k.factorial:ℝ)
  apply hh.mono'
  · exact ((hF.continuous.comp (by fun_prop : Continuous (WithLp.toLp 2 : (κ→ℝ)→EuclideanSpace ℝ κ))).abs.pow k).aestronglyMeasurable
  · filter_upwards [] with g
    simpa only [Real.norm_eq_abs,abs_pow,abs_abs,one_pow,div_one,Pi.add_apply] using
      pow_le_exponential_pair (F (WithLp.toLp 2 g)) (by norm_num : (0:ℝ)<1) k

lemma gaussianProduct_integrable_pow_lipschitz {F : EuclideanSpace ℝ κ→ℝ}
    {L : NNReal} (hF : LipschitzWith L F) (k : ℕ) :
    Integrable (fun g : κ→ℝ=>F (WithLp.toLp 2 g)^k) (Measure.pi (fun _=>gaussianReal 0 1)) := by
  apply (gaussianProduct_integrable_abs_pow_lipschitz hF k).mono'
  · exact ((hF.continuous.comp (by fun_prop : Continuous (WithLp.toLp 2 : (κ→ℝ)→EuclideanSpace ℝ κ))).pow k).aestronglyMeasurable
  · filter_upwards [] with g
    simp only [Real.norm_eq_abs,abs_pow,le_refl]
end SKGap
end
end

section
noncomputable section
namespace SKGap
open Real Matrix MeasureTheory ProbabilityTheory Set
open scoped BigOperators Matrix.Norms.Frobenius
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]

def matrixEntryMean (F : EuclideanSpace ℝ κ→Matrix ι ι ℝ) : Matrix ι ι ℝ :=
  fun i k=>∫ g : κ→ℝ,F (WithLp.toLp 2 g) i k ∂Measure.pi (fun _=>gaussianReal 0 1)
def matrixCentered (F : EuclideanSpace ℝ κ→Matrix ι ι ℝ) (x : EuclideanSpace ℝ κ) :=
  F x-matrixEntryMean F

lemma matrixCentered_lipschitz {F : EuclideanSpace ℝ κ→Matrix ι ι ℝ}
    {L : NNReal} (hF : LipschitzWith L F) : LipschitzWith L (matrixCentered F) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simpa only [matrixCentered,dist_sub_right] using hF.dist_le_mul x y

lemma matrixEntry_lip {F : EuclideanSpace ℝ κ→Matrix ι ι ℝ}
    {L : NNReal} (hF : LipschitzWith L F) (i k : ι) : LipschitzWith L (fun x=>F x i k) := by
  simpa only [one_mul,Function.comp_def] using (matrixEntry_lipschitz i k).comp hF

lemma diagonalCentered_lip {F : EuclideanSpace ℝ κ→Matrix ι ι ℝ}
    {L : NNReal} (hF : LipschitzWith L F) : LipschitzWith L (fun x=>diagonalSeminorm (matrixCentered F x)) := by
  simpa only [one_mul,Function.comp_def] using diagonalSeminorm_lipschitz.comp (matrixCentered_lipschitz hF)
lemma offDiagonalCentered_lip {F : EuclideanSpace ℝ κ→Matrix ι ι ℝ}
    {L : NNReal} (hF : LipschitzWith L F) : LipschitzWith L (fun x=>offDiagonalSeminorm (matrixCentered F x)) := by
  simpa only [one_mul,Function.comp_def] using offDiagonalSeminorm_lipschitz.comp (matrixCentered_lipschitz hF)

lemma matrixCentered_even_moment {F : EuclideanSpace ℝ κ→Matrix ι ι ℝ}
    {L : NNReal} (hF : LipschitzWith L F) (hL : 0<L) (i b : ι) (k : ℕ) :
    (∫ g : κ→ℝ,(matrixCentered F (WithLp.toLp 2 g) i b)^(2*k) ∂Measure.pi (fun _=>gaussianReal 0 1))≤
      (2*((2*k).factorial:ℝ)*exp (π^2/8))*(L:ℝ)^(2*k) := by
  have hh := gaussianProduct_abs_centered_moment (matrixEntry_lip hF i b) hL (2*k)
  simpa only [matrixCentered,matrixEntryMean,Matrix.sub_apply,pow_mul,sq_abs] using hh

lemma diagonalCentered_second_moment {F : EuclideanSpace ℝ κ→Matrix ι ι ℝ}
    {L : NNReal} (hF : LipschitzWith L F) (hL : 0<L) :
    (∫ g : κ→ℝ,diagonalSeminorm (matrixCentered F (WithLp.toLp 2 g))^2 ∂Measure.pi (fun _=>gaussianReal 0 1))≤
      (Fintype.card ι:ℝ)*(4*exp (π^2/8))*(L:ℝ)^2 := by
  simp_rw [diagonalSeminorm_sq]
  rw [integral_finsetSum _ (fun i _=>gaussianProduct_integrable_pow_lipschitz (matrixEntry_lip (matrixCentered_lipschitz hF) i i) 2)]
  apply (Finset.sum_le_sum (fun i _=>matrixCentered_even_moment hF hL i i 1)).trans_eq
  norm_num [Finset.sum_const,mul_assoc]

lemma offDiagonalCentered_fourth_moment {F : EuclideanSpace ℝ κ→Matrix ι ι ℝ}
    {L : NNReal} (hF : LipschitzWith L F) (hL : 0<L) :
    (∫ g : κ→ℝ,offDiagonalSeminorm (matrixCentered F (WithLp.toLp 2 g))^4 ∂Measure.pi (fun _=>gaussianReal 0 1))≤
      (Fintype.card ι:ℝ)^2*(48*exp (π^2/8))*(L:ℝ)^4 := by
  simp_rw [offDiagonalSeminorm_fourth]
  have hi (p : ι×ι) : Integrable (fun g : κ→ℝ=>if p.1=p.2 then 0 else matrixCentered F (WithLp.toLp 2 g) p.1 p.2^4)
      (Measure.pi (fun _=>gaussianReal 0 1)) := by
    split_ifs
    · exact integrable_const _
    · exact gaussianProduct_integrable_pow_lipschitz (matrixEntry_lip (matrixCentered_lipschitz hF) p.1 p.2) 4
  rw [integral_finsetSum _ (fun p _=>hi p)]
  have hb (p : ι×ι) : (∫ g : κ→ℝ,(if p.1=p.2 then 0 else matrixCentered F (WithLp.toLp 2 g) p.1 p.2^4)
      ∂Measure.pi (fun _=>gaussianReal 0 1)) ≤ (48*exp (π^2/8))*(L:ℝ)^4 := by
    split_ifs
    · simp only [integral_zero];positivity
    · have hh := matrixCentered_even_moment hF hL p.1 p.2 2
      norm_num at hh
      exact hh
  apply (Finset.sum_le_sum (fun p _=>hb p)).trans_eq
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_prod,nsmul_eq_mul,Nat.cast_mul]
  ring

lemma gaussianProduct_jensen_pow {F : EuclideanSpace ℝ κ→ℝ} {L : NNReal}
    (hF : LipschitzWith L F) (hpos : ∀ x,0≤F x) (k : ℕ) :
    (∫ g : κ→ℝ,F (WithLp.toLp 2 g) ∂Measure.pi (fun _=>gaussianReal 0 1))^k≤
      ∫ g : κ→ℝ,F (WithLp.toLp 2 g)^k ∂Measure.pi (fun _=>gaussianReal 0 1) := by
  exact (convexOn_pow (𝕜:=ℝ) k).map_integral_le (by fun_prop) isClosed_Ici
    (ae_of_all _ (fun g=>hpos (WithLp.toLp 2 g))) (gaussianProduct_integrable_lipschitz hF)
    (gaussianProduct_integrable_pow_lipschitz hF k)

def matrixNormConstant : ℝ := 1+48*exp (π^2/8)

omit [Fintype ι] [DecidableEq ι] [Fintype κ] in
lemma matrixNormConstant_bounds : 1≤ matrixNormConstant ∧
    4*exp (π^2/8)≤ matrixNormConstant^2 ∧ 48*exp (π^2/8)≤ matrixNormConstant^4 := by
  have hE := (exp_pos (π^2/8)).le
  have hC : 1≤ matrixNormConstant := by unfold matrixNormConstant;linarith
  have hC2 : matrixNormConstant≤ matrixNormConstant^2 := by
    simpa only [pow_one] using pow_le_pow_right₀ hC (by decide : 1≤2)
  have hC4 : matrixNormConstant≤ matrixNormConstant^4 := by
    simpa only [pow_one] using pow_le_pow_right₀ hC (by decide : 1≤4)
  refine ⟨hC,?_,?_⟩ <;> unfold matrixNormConstant at * <;> linarith

lemma gaussianProduct_centered_matrix_norms {F : EuclideanSpace ℝ κ→Matrix ι ι ℝ}
    {L : NNReal} (hF : LipschitzWith L F) (hL : 0<L) :
    (∫ g : κ→ℝ,diagonalSeminorm (matrixCentered F (WithLp.toLp 2 g)) ∂Measure.pi (fun _=>gaussianReal 0 1))≤
      matrixNormConstant*sqrt (Fintype.card ι)*(L:ℝ) ∧
    (∫ g : κ→ℝ,offDiagonalSeminorm (matrixCentered F (WithLp.toLp 2 g)) ∂Measure.pi (fun _=>gaussianReal 0 1))≤
      matrixNormConstant*sqrt (Fintype.card ι)*(L:ℝ) := by
  let : Fact (1≤(4:ENNReal)) := ⟨by norm_num⟩
  have hC0 : 0≤ matrixNormConstant := zero_le_one.trans matrixNormConstant_bounds.1
  have hcn : (0:ℝ)≤Fintype.card ι := Nat.cast_nonneg _
  constructor
  · apply le_of_pow_le_pow_left₀ (by decide : 2≠0) (by positivity)
    have hJ := gaussianProduct_jensen_pow (diagonalCentered_lip hF) (fun x=>norm_nonneg (diagonalVector (matrixCentered F x))) 2
    apply (hJ.trans (diagonalCentered_second_moment hF hL)).trans
    rw [mul_pow,mul_pow,sq_sqrt hcn]
    have hh := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left matrixNormConstant_bounds.2.1 hcn) (sq_nonneg (L:ℝ))
    nlinarith only [hh]
  · apply le_of_pow_le_pow_left₀ (by decide : 4≠0) (by positivity)
    have hJ := gaussianProduct_jensen_pow (offDiagonalCentered_lip hF) (fun x=>norm_nonneg (offDiagonalVector (matrixCentered F x))) 4
    apply (hJ.trans (offDiagonalCentered_fourth_moment hF hL)).trans
    have hs : sqrt (Fintype.card ι)^4=(Fintype.card ι:ℝ)^2 := by
      calc
        _ = (sqrt (Fintype.card ι)^2)^2 := by ring
        _ = _ := by rw [sq_sqrt hcn]
    rw [mul_pow,mul_pow,hs]
    have hh := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left matrixNormConstant_bounds.2.2 (sq_nonneg (Fintype.card ι:ℝ))) (by positivity : (0:ℝ)≤(L:ℝ)^4)
    nlinarith only [hh]
end SKGap
end
end

end OAI
