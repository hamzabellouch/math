import OAI.Analysis.FreeEntropy.MatrixReparam

namespace OAI

universe u1 u2 u3 u4

noncomputable section
open MeasureTheory ProbabilityTheory Finset Filter
open scoped Classical Topology
namespace FiniteEntropySeparation
 theorem complex_mean_square_bound {ι : Type u1} [Fintype ι] [DecidableEq ι]
    {f : (ι → ℝ) → ℂ} (hf : IsComplexPolynomial f) (z : ℂ) :
    (∫ x, ‖f x-z‖^2 ∂productGaussian ι) ≤
        2*(∫ x, ‖f x-∫ y, f y ∂productGaussian ι‖^2 ∂productGaussian ι)+2*‖(∫ y, f y ∂productGaussian ι)-z‖^2 := by
  let a := ∫ y, f y ∂productGaussian ι
  have hg := (hf.sub (IsComplexPolynomial.const a)).norm_sq.integrable
  calc
    _ ≤ ∫ x, 2*‖f x-a‖^2+2*‖a-z‖^2 ∂productGaussian ι := by
      apply integral_mono ((hf.sub (IsComplexPolynomial.const z)).norm_sq.integrable) ((hg.const_mul 2).add (integrable_const _))
      intro x
      have ht : ‖f x-z‖ ≤ ‖f x-a‖+‖a-z‖ := by
        simpa only [sub_add_sub_cancel] using norm_add_le (f x-a) (a-z)
      have hp := pow_le_pow_left₀ (norm_nonneg _) ht 2
      change ‖f x-z‖^2 ≤ 2*‖f x-a‖^2+2*‖a-z‖^2
      nlinarith [sq_nonneg (‖f x-a‖-‖a-z‖)]
    _ = _ := by rw [integral_add (hg.const_mul _) (integrable_const _),integral_const_mul]; simp [a]
 theorem real_tendsto_zero_of_inv_sq {D : ℕ → ℕ} (hD : Tendsto D atTop atTop) (C : ℝ) :
    Tendsto (fun k => C/(D k:ℝ)^2) atTop (𝓝 0) := by
  have hc : Tendsto (fun k => (D k:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop.comp hD
  have hi := tendsto_inv_atTop_zero.comp (tendsto_pow_atTop (by norm_num : (2:ℕ) ≠ 0) |>.comp hc)
  simpa [div_eq_mul_inv] using tendsto_const_nhds.mul hi
 theorem matrixTraceWord_mean_square_tendsto {α : Type u2} {n : ℕ} {D : ℕ → ℕ}
    (hD0 : ∀ k,0<D k) (hD : Tendsto D atTop atTop)
    (A : (k : ℕ) → α → Matrix (Fin (D k)) (Fin (D k)) ℂ) {R : ℝ} (hR : 0 ≤ R)
    (hA : ∀ k a, matrixOpNorm (A k a) ≤ R) (w : List (α ⊕ Fin n)) {z : ℂ}
    (hm : Tendsto (fun k => expectedMatrixWord A k w) atTop (𝓝 z)) :
    Tendsto (fun k => ∫ x, ‖matrixTraceWord (jointMatrix (A k) x) w-z‖^2 ∂productGaussian (MatrixIndex n (D k))) atTop (𝓝 0) := by
  have hvar : Tendsto (fun k => ∫ x, ‖matrixTraceWord (jointMatrix (A k) x) w-expectedMatrixWord A k w‖^2 ∂productGaussian (MatrixIndex n (D k))) atTop (𝓝 0) := by
    apply squeeze_zero (fun k => integral_nonneg (fun _ => sq_nonneg _))
      (fun k => (matrixTraceWord_variance_bound (hD0 k) (A k) hR (hA k) w).trans_eq (by ring))
      (real_tendsto_zero_of_inv_sq hD ((w.length:ℝ)^2*jointMomentBound n R (2*(w.length-1))))
  have hb : Tendsto (fun k => 2*(∫ x, ‖matrixTraceWord (jointMatrix (A k) x) w-expectedMatrixWord A k w‖^2 ∂productGaussian (MatrixIndex n (D k)))+2*‖expectedMatrixWord A k w-z‖^2) atTop (𝓝 0) := by
    have hh := (hvar.const_mul 2).add (((hm.sub_const z).norm.pow 2).const_mul 2)
    simpa using hh
  exact squeeze_zero (fun k => integral_nonneg (fun _ => sq_nonneg _))
    (fun k => complex_mean_square_bound (matrixTraceWord_polynomial (A k) w) z) hb
 theorem probability_error_le_mean_square {Ω : Type u3} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    {f : Ω → ℂ} {z : ℂ} {ε : ℝ} (hε : 0 < ε) (hi : Integrable (fun x => ‖f x-z‖^2) μ) :
    μ.real {x | ε ≤ ‖f x-z‖} ≤ (∫ x, ‖f x-z‖^2 ∂μ)/ε^2 := by
  have he : {x | ε ≤ ‖f x-z‖} = {x | ε^2 ≤ ‖f x-z‖^2} := by
    ext x; simp only [Set.mem_ofPred_eq]; exact (sq_le_sq₀ hε.le (norm_nonneg _)).symm
  rw [he]
  exact (le_div_iff₀ (sq_pos_of_pos hε)).mpr (by
    simpa [mul_comm] using mul_meas_ge_le_integral_of_nonneg (ae_of_all _ (fun x => sq_nonneg ‖f x-z‖)) hi (ε^2))
 theorem matrixTraceWord_probability_tendsto {α : Type u4} {n : ℕ} {D : ℕ → ℕ}
    (hD0 : ∀ k,0<D k) (hD : Tendsto D atTop atTop)
    (A : (k : ℕ) → α → Matrix (Fin (D k)) (Fin (D k)) ℂ) {R : ℝ} (hR : 0 ≤ R)
    (hA : ∀ k a, matrixOpNorm (A k a) ≤ R) (w : List (α ⊕ Fin n)) {z : ℂ}
    (hm : Tendsto (fun k => expectedMatrixWord A k w) atTop (𝓝 z)) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun k => (productGaussian (MatrixIndex n (D k))).real {x | ε ≤ ‖matrixTraceWord (jointMatrix (A k) x) w-z‖}) atTop (𝓝 0) := by
  apply squeeze_zero (fun k => measureReal_nonneg)
    (fun k => probability_error_le_mean_square _ hε ((matrixTraceWord_polynomial (A k) w).sub (IsComplexPolynomial.const z)).norm_sq.integrable)
  simpa using (matrixTraceWord_mean_square_tendsto hD0 hD A hR hA w hm).div_const (ε^2)
end FiniteEntropySeparation

end

end OAI
