import Mathlib
import OAI.Probability.SKGap.Localization.ProjectedReal
import OAI.Probability.SKGap.Localization.Bilinear

namespace OAI

section
noncomputable section
namespace SKGap
open Matrix MeasureTheory ProbabilityTheory Real Set
open scoped BigOperators Matrix.Norms.Frobenius NNReal ENNReal
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
lemma gaussianCoordinate_mean (a : MatrixCoordinates ι) :
    (∫ g : MatrixCoordinates ι → ℝ, g a ∂Measure.pi (fun _ => gaussianReal 0 1)) = 0 := by
  rw [integral_comp_eval (μ := fun _ : MatrixCoordinates ι => gaussianReal 0 1) (i := a)
    (by fun_prop : AEStronglyMeasurable (fun x : ℝ => x) (gaussianReal 0 1))]
  exact integral_id_gaussianReal

omit [DecidableEq ι] in
lemma goeEntry_integral (r : ℝ) (i k : ι) :
    (∫ g, goeMatrix r g i k ∂Measure.pi (fun _ : MatrixCoordinates ι => gaussianReal 0 1)) = 0 := by
  simp only [goeMatrix,integral_const_mul]
  rw [integral_add ((gaussianCoordinate_memLp (.inl (i,k))).integrable (by norm_num))
    ((gaussianCoordinate_memLp (.inl (k,i))).integrable (by norm_num))]
  simp only [gaussianCoordinate_mean,add_zero,mul_zero]

omit [Fintype ι] in
lemma signConjugate_diagonal (s : ι → ℝ) (hs : ∀ i, s i^2=1) (d : ι → ℝ) :
    signConjugate s (diagonal d)=diagonal d := by
  ext i k
  by_cases h : i=k
  · subst k
    simp only [signConjugate,diagonal_apply_eq]
    rw [← pow_two,hs,one_mul]
  · simp [signConjugate,diagonal_apply_ne _ h]

omit [Fintype ι] [DecidableEq ι] in
lemma signConjugate_sub (s : ι → ℝ) (M N : Matrix ι ι ℝ) :
    signConjugate s (M-N) = signConjugate s M-signConjugate s N := by
  ext i k; simp [signConjugate,mul_sub]

omit [Fintype ι] [DecidableEq ι] in
lemma signConjugate_smul (s : ι → ℝ) (w : ℝ) (M : Matrix ι ι ℝ) :
    signConjugate s (w • M) = w • signConjugate s M := by
  ext i k; simp only [signConjugate,Matrix.smul_apply,smul_eq_mul]; ring

def affineRight (F : Matrix ι ι ℝ → Matrix ι ι ℝ) (d e : ι → ℝ)
    (w : ℝ) (M : Matrix ι ι ℝ) : Matrix ι ι ℝ := F M*diagonal d-diagonal e-w • M

lemma affineRight_sign (F : Matrix ι ι ℝ → Matrix ι ι ℝ) (d e : ι → ℝ) (w : ℝ)
    (hF : ∀ (s : ι → ℝ), (∀ i, s i^2=1) → ∀ M,
      F (signConjugate s M)=signConjugate s (F M))
    (s : ι → ℝ) (hs : ∀ i, s i^2=1) (M : Matrix ι ι ℝ) :
    affineRight F d e w (signConjugate s M)=signConjugate s (affineRight F d e w M) := by
  simp only [affineRight,signConjugate_sub,signConjugate_smul,signConjugate_mul s hs,
    signConjugate_diagonal s hs,hF s hs]

lemma affineRight_lip (F : Matrix ι ι ℝ → Matrix ι ι ℝ) (d e : ι → ℝ) (w : ℝ)
    {L D : ℝ} (hD : 0 ≤ D) (hd : ∀ i, |d i| ≤ D)
    (hF : ∀ M N, ‖F M-F N‖ ≤ L*‖M-N‖) (M N : Matrix ι ι ℝ) :
    ‖affineRight F d e w M-affineRight F d e w N‖ ≤ (L*D+|w|)*‖M-N‖ := by
  have he : affineRight F d e w M-affineRight F d e w N =
      (F M-F N)*diagonal d-w • (M-N) := by
    simp only [affineRight,sub_mul,smul_sub]; abel
  rw [he]
  calc
    _ ≤ ‖(F M-F N)*diagonal d‖+‖w • (M-N)‖ := norm_sub_le _ _
    _ ≤ ‖F M-F N‖*opNorm (diagonal d)+|w| *‖M-N‖ := by
      rw [norm_smul,Real.norm_eq_abs]
      exact add_le_add (frobenius_mul_le_opNorm_right (F M-F N) (diagonal d)) le_rfl
    _ ≤ (L*‖M-N‖)*D+|w| *‖M-N‖ := add_le_add
      (mul_le_mul (hF M N) (opNorm_diagonal_le hD hd) (norm_nonneg _) (le_trans (norm_nonneg _) (hF M N))) le_rfl
    _ = _ := by ring

lemma affineRight_diag (F : Matrix ι ι ℝ → Matrix ι ι ℝ) (d e : ι → ℝ)
    (w : ℝ) (M : Matrix ι ι ℝ) (i : ι) :
    affineRight F d e w M i i=F M i i*d i-e i-w*M i i := by
  simp only [affineRight,Matrix.sub_apply,Matrix.mul_diagonal,diagonal_apply_eq,
    Matrix.smul_apply,smul_eq_mul]

lemma affineRight_bias (r : ℝ) (F : Matrix ι ι ℝ → Matrix ι ι ℝ) (d e k : ι → ℝ) (w : ℝ)
    {ε D : ℝ} (_hD : 0 ≤ D) (hd : ∀ i, |d i| ≤ D)
    (hI : ∀ i k, Integrable (fun g => F (goeMatrix r g) i k)
      (Measure.pi (fun _ : MatrixCoordinates ι => gaussianReal 0 1)))
    (hF : ∀ i, |(∫ g, F (goeMatrix r g) i i
      ∂Measure.pi (fun _ : MatrixCoordinates ι => gaussianReal 0 1))-k i| ≤ ε) (i : ι) :
    |(∫ g, affineRight F d e w (goeMatrix r g) i i
      ∂Measure.pi (fun _ : MatrixCoordinates ι => gaussianReal 0 1))-(k i*d i-e i)| ≤ ε*D := by
  simp_rw [affineRight_diag]
  rw [integral_sub (f := fun g => F (goeMatrix r g) i i*d i-e i)
    (g := fun g => w*goeMatrix r g i i)
    ((hI i i).mul_const (d i) |>.sub (integrable_const (e i)))
    ((goeEntry_memLp r i i).integrable (by norm_num) |>.const_mul w),
    integral_sub (f := fun g => F (goeMatrix r g) i i*d i) (g := fun _ => e i)
    ((hI i i).mul_const (d i)) (integrable_const (e i)),
    integral_mul_const,integral_const,integral_const_mul,goeEntry_integral]
  simp only [probReal_univ,one_smul,mul_zero,sub_zero]
  rw [show (∫ g, F (goeMatrix r g) i i ∂Measure.pi (fun _ : MatrixCoordinates ι => gaussianReal 0 1))*d i-e i-
      (k i*d i-e i) = ((∫ g, F (goeMatrix r g) i i ∂Measure.pi (fun _ : MatrixCoordinates ι => gaussianReal 0 1))-k i)*d i by ring,
    abs_mul]
  exact mul_le_mul (hF i) (hd i) (abs_nonneg _) (le_trans (abs_nonneg _) (hF i))

lemma affineRight_concentration [Nonempty ι] {j L U ε D t : ℝ}
    (hj : 0 < j) (hL : 0 ≤ L) (hU : 0 ≤ U) (hε : 0 ≤ ε) (hD : 0 ≤ D) (ht : 0 ≤ t)
    (F : Matrix ι ι ℝ → Matrix ι ι ℝ) (d e k : ι → ℝ) (w : ℝ)
    (hd : ∀ i, |d i| ≤ D)
    (hF : ∀ (s : ι → ℝ), (∀ i, s i^2=1) → ∀ M,
      F (signConjugate s M)=signConjugate s (F M))
    (hLip : ∀ M N, ‖F M-F N‖ ≤ L*‖M-N‖)
    (hk : ∀ i, |(∫ g, F (goeMatrix (j/(Fintype.card ι:ℝ)) g) i i
      ∂Measure.pi (fun _ : MatrixCoordinates ι => gaussianReal 0 1))-k i| ≤ ε)
    (u v : EuclideanSpace ℝ ι) (hu : ‖u‖ ≤ U) (hv : ‖v‖ ≤ U) :
    (Measure.pi (fun _ : MatrixCoordinates ι => gaussianReal 0 1)).real
      {g | (ε*D)*U^2+t ≤ |matrixBilinear (affineRight F d e w (goeMatrix (j/(Fintype.card ι:ℝ)) g)-
        diagonal (fun i => k i*d i-e i)) u v|} ≤
      2*exp (-(Fintype.card ι:ℝ)*t^2/(π^2*((L*D+|w|+1)*(U+1)^2)^2*j)) := by
  exact goe_bilinear_concentration hj (by positivity) hU (mul_nonneg hε hD) ht
    (affineRight F d e w) (affineRight_sign F d e w hF)
    (affineRight_lip F d e w hD hd hLip) _
    (affineRight_bias _ F d e k w hD hd (goe_entries_integrable _ F hL hLip) hk)
    u v hu hv
end SKGap
end
end

end OAI
