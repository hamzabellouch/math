import OAI.Analysis.FreeEntropy.GUEMoments

namespace OAI

universe u1 u2

noncomputable section
open MeasureTheory ProbabilityTheory Finset
open scoped Classical
namespace FiniteEntropySeparation
 def jointNoiseBound {n d : ℕ} (R : ℝ) (x : MatrixIndex n d → ℝ) : ℝ := R+∑ i, matrixOpNorm (gueMatrix x i)
 def jointMomentBound (n : ℕ) (R : ℝ) : ℕ → ℝ
   | 0 => 1
   | m+1 => (n+1:ℝ)^m*(R^(m+1)+(n:ℝ)*gaussianMomentMajorant m)
 theorem jointNoiseBound_nonneg {n d : ℕ} {R : ℝ} (hR : 0 ≤ R) (x : MatrixIndex n d → ℝ) :
    0 ≤ jointNoiseBound R x := add_nonneg hR (sum_nonneg (fun _ _ => norm_nonneg _))
 theorem jointNoiseBound_measurable {n d : ℕ} (R : ℝ) : Measurable (jointNoiseBound (n := n) (d := d) R) :=
   measurable_const.add (Finset.measurable_sum _ (fun i _ => gueMatrix_norm_measurable i))
 theorem jointMatrix_norm_bound {α : Type u1} {n d : ℕ} (A : α → Matrix (Fin d) (Fin d) ℂ) {R : ℝ} (hR : 0 ≤ R)
    (hA : ∀ a, matrixOpNorm (A a) ≤ R) (x : MatrixIndex n d → ℝ) (a : α ⊕ Fin n) :
    matrixOpNorm (jointMatrix A x a) ≤ jointNoiseBound R x := by
  cases a with
  | inl a =>
    change matrixOpNorm (A a) ≤ R + ∑ i, matrixOpNorm (gueMatrix x i)
    exact (hA a).trans (le_add_of_nonneg_right (sum_nonneg (fun i _ => matrixOpNorm_nonneg (gueMatrix x i))))
  | inr i =>
    change matrixOpNorm (gueMatrix x i) ≤ R + ∑ j, matrixOpNorm (gueMatrix x j)
    have hl : matrixOpNorm (gueMatrix x i) ≤ ∑ j, matrixOpNorm (gueMatrix x j) :=
      single_le_sum (fun j _ => matrixOpNorm_nonneg (gueMatrix x j)) (mem_univ i)
    exact hl.trans (le_add_of_nonneg_left hR)
 theorem jointNoiseBound_power {n d : ℕ} {R : ℝ} (hR : 0 ≤ R) (x : MatrixIndex n d → ℝ) (m : ℕ) :
    jointNoiseBound R x^(m+1) ≤ (n+1:ℝ)^m * (R^(m+1)+∑ i, matrixOpNorm (gueMatrix x i)^(m+1)) := by
  let f : Option (Fin n) → ℝ := Option.elim' R (fun i => matrixOpNorm (gueMatrix x i))
  have hf : ∀ i ∈ (univ : Finset (Option (Fin n))), 0 ≤ f i := by
    intro i _; cases i <;> simp [f,hR,matrixOpNorm_nonneg]
  simpa [f, Fintype.sum_option, jointNoiseBound, add_comm] using pow_sum_le_card_mul_sum_pow hf m
 theorem jointNoiseBound_moment {n d : ℕ} (hd : 0 < d) {R : ℝ} (hR : 0 ≤ R) (m : ℕ) :
    Integrable (fun x => jointNoiseBound R x^m) (productGaussian (MatrixIndex n d)) ∧
    (∫ x, jointNoiseBound R x^m ∂productGaussian (MatrixIndex n d)) ≤ jointMomentBound n R m := by
  cases m with
  | zero => simp [jointMomentBound]
  | succ m =>
    have hi (i : Fin n) := (gueMatrix_norm_moment hd i m).1
    have hsum : Integrable (fun x => ∑ i : Fin n, matrixOpNorm (gueMatrix x i)^(m+1)) (productGaussian (MatrixIndex n d)) := integrable_finsetSum _ (fun i _ => hi i)
    have hbig := ((integrable_const (R^(m+1))).add hsum).const_mul ((n+1:ℝ)^m)
    have hsmall : Integrable (fun x : MatrixIndex n d → ℝ => jointNoiseBound R x^(m+1)) (productGaussian (MatrixIndex n d)) := by
      apply hbig.mono' ((jointNoiseBound_measurable R).pow_const _).aestronglyMeasurable
      exact ae_of_all _ (fun x => by rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (jointNoiseBound_nonneg hR x) _)]; exact jointNoiseBound_power hR x m)
    refine ⟨hsmall, ?_⟩
    calc
      _ ≤ ∫ x : MatrixIndex n d → ℝ, ((n+1:ℝ)^m)*(R^(m+1)+∑ i, matrixOpNorm (gueMatrix x i)^(m+1)) ∂productGaussian (MatrixIndex n d) :=
        integral_mono hsmall hbig (fun x => jointNoiseBound_power hR x m)
      _ = (n+1:ℝ)^m*(R^(m+1)+∑ i, ∫ x, matrixOpNorm (gueMatrix x i)^(m+1) ∂productGaussian (MatrixIndex n d)) := by
        rw [integral_const_mul, integral_add (integrable_const _) hsum, integral_finsetSum _ (fun i _ => hi i)]; simp
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply add_le_add_right
        calc
          _ ≤ ∑ _i : Fin n, gaussianMomentMajorant m := sum_le_sum (fun i _ => (gueMatrix_norm_moment hd i m).2)
          _ = _ := by simp
 theorem matrixTraceWord_variance_bound {α : Type u2} {n d : ℕ} (hd : 0 < d)
    (A : α → Matrix (Fin d) (Fin d) ℂ) {R : ℝ} (hR : 0 ≤ R) (hA : ∀ a, matrixOpNorm (A a) ≤ R)
    (w : List (α ⊕ Fin n)) :
    (∫ x, ‖matrixTraceWord (jointMatrix A x) w - ∫ y, matrixTraceWord (jointMatrix A y) w ∂productGaussian (MatrixIndex n d)‖^2 ∂productGaussian (MatrixIndex n d)) ≤
      (w.length:ℝ)^2/(d:ℝ)^2 * jointMomentBound n R (2*(w.length-1)) := by
  let f := fun x : MatrixIndex n d → ℝ => matrixTraceWord (jointMatrix A x) w
  have hf : IsComplexPolynomial f := matrixTraceWord_polynomial A w
  have hi (q : MatrixIndex n d) := ((hf.derivative q).norm_sq).integrable
  calc
    _ ≤ ∑ q, ∫ x, ‖complexCoordinateDerivative f q x‖^2 ∂productGaussian (MatrixIndex n d) := hf.poincare
    _ = ∫ x, ∑ q, ‖complexCoordinateDerivative f q x‖^2 ∂productGaussian (MatrixIndex n d) := (integral_finsetSum _ (fun q _ => hi q)).symm
    _ ≤ ∫ x, ((w.length:ℝ)^2/(d:ℝ)^2)*jointNoiseBound R x^(2*(w.length-1)) ∂productGaussian (MatrixIndex n d) := by
      apply integral_mono (integrable_finsetSum _ (fun q _ => hi q)) ((jointNoiseBound_moment hd hR _).1.const_mul _)
      intro x
      exact matrixTraceWord_gradient_bound hd A w x (jointNoiseBound_nonneg hR x) (fun a _ => jointMatrix_norm_bound A hR hA x a)
    _ = ((w.length:ℝ)^2/(d:ℝ)^2)*(∫ x, jointNoiseBound R x^(2*(w.length-1)) ∂productGaussian (MatrixIndex n d)) := integral_const_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left (jointNoiseBound_moment hd hR _).2 (by positivity)
end FiniteEntropySeparation

end

end OAI
