import OAI.Analysis.FreeEntropy.GUEDerivative

namespace OAI

universe u1 u2 u3

noncomputable section
open MeasureTheory ProbabilityTheory Finset
open scoped Classical
namespace FiniteEntropySeparation
 theorem norm_sum_sq_le {ι : Type u1} (s : Finset ι) (f : ι → ℂ) :
    ‖∑ i ∈ s, f i‖^2 ≤ (s.card:ℝ)*∑ i ∈ s, ‖f i‖^2 := by
  exact (pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le s f) 2).trans (sq_sum_le_card_mul_sum_sq (s := s) (f := fun i => ‖f i‖))
 theorem basisNoise_trace_bound {α : Type u2} {n d : ℕ} (a : α ⊕ Fin n) (D : Matrix (Fin d) (Fin d) ℂ) :
    (∑ q : MatrixIndex n d, ‖(if a=Sum.inr q.1 then Matrix.trace (hermitianBasis q.2.1 q.2.2*D) else 0 : ℂ)‖^2) ≤
      (d:ℝ)*matrixOpNorm D^2 := by
  cases a with
  | inl a => simp; positivity
  | inr i =>
    simpa [Fintype.sum_prod_type, apply_ite, sum_ite_irrel, sum_ite_eq] using hermitianBasis_trace_bound D
 theorem matrixTraceWord_gradient_bound {α : Type u3} {n d : ℕ} (hd : 0 < d)
    (A : α → Matrix (Fin d) (Fin d) ℂ) (w : List (α ⊕ Fin n))
    (x : MatrixIndex n d → ℝ) {K : ℝ} (hK : 0 ≤ K) (hA : ∀ i ∈ w, matrixOpNorm (jointMatrix A x i) ≤ K) :
    (∑ q, ‖complexCoordinateDerivative (fun y => matrixTraceWord (jointMatrix A y) w) q x‖^2) ≤
      (w.length:ℝ)^2/(d:ℝ)^2 * K^(2*(w.length-1)) := by
  have hd' : (d:ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hd
  have hc : ‖((d:ℂ)⁻¹*(Real.sqrt d:ℂ)⁻¹)‖^2 = (d:ℝ)⁻¹^3 := by
    simp only [norm_mul, mul_pow, norm_inv, Complex.norm_natCast, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), inv_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
    field_simp
  simp only [norm_mul, mul_pow] at hc
  simp_rw [matrixTraceWord_derivative, norm_mul, mul_pow, hc]
  rw [← mul_sum]
  calc
    _ ≤ (d:ℝ)⁻¹^3 * ∑ q : MatrixIndex n d, (w.length:ℝ)*∑ r : Fin w.length,
          ‖(if w[r.val]=Sum.inr q.1 then Matrix.trace (hermitianBasis q.2.1 q.2.2*cyclicMatrixWord (jointMatrix A x) w r) else 0 : ℂ)‖^2 := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply sum_le_sum
      intro q _
      simpa using norm_sum_sq_le univ (fun r : Fin w.length => if w[r.val]=Sum.inr q.1 then Matrix.trace (hermitianBasis q.2.1 q.2.2*cyclicMatrixWord (jointMatrix A x) w r) else 0)
    _ = (d:ℝ)⁻¹^3 * ((w.length:ℝ)*∑ r : Fin w.length, ∑ q : MatrixIndex n d,
          ‖(if w[r.val]=Sum.inr q.1 then Matrix.trace (hermitianBasis q.2.1 q.2.2*cyclicMatrixWord (jointMatrix A x) w r) else 0 : ℂ)‖^2) := by rw [← mul_sum, sum_comm]
    _ ≤ (d:ℝ)⁻¹^3 * ((w.length:ℝ)*∑ _r : Fin w.length, (d:ℝ)*(K^(w.length-1))^2) := by
      gcongr with r
      exact (basisNoise_trace_bound _ _).trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (matrixOpNorm_nonneg _) (cyclicMatrixWord_bound _ _ _ hK hA) 2) (Nat.cast_nonneg _))
    _ = _ := by
      simp only [sum_const, card_fin, nsmul_eq_mul, ← pow_mul]
      rw [Nat.mul_comm (w.length-1) 2]
      field_simp
end FiniteEntropySeparation

end

end OAI
