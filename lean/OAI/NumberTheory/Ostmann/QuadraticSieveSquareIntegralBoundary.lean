import OAI.NumberTheory.Ostmann.QuadraticSieveSquareIntegralDamping

namespace OAI

noncomputable section
namespace Ostmann.QuadraticSieve
open MeasureTheory Filter Complex Set
open scoped SchwartzMap FourierTransform Topology

def squareGaussianValue (ε a t : ℝ) : ℂ :=
  ((Real.pi : ℂ)/squareGaussianParameter ε a t)^(1/2 : ℂ)

theorem squareGaussianParameter_ne_zero {a t : ℝ} (ha : a≠0) (ht : t≠0) (ε : ℝ) :
    squareGaussianParameter ε a t≠0 := by
  intro h
  have hi := congrArg Complex.im h
  simp only [squareGaussianParameter_im,Complex.zero_im] at hi
  exact (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero) ha) ht) hi

theorem squareGaussianValue_bound {a δ t : ℝ} (ha : a≠0) (hδ : 0<δ) (ht : δ≤t) (ε : ℝ) :
    ‖squareGaussianValue ε a t‖ ≤
      (Real.pi/(2*Real.pi*|a| *δ))^(1/2 : ℝ) := by
  have hapos : 0 < |a| := abs_pos.mpr ha
  have htpos : 0<t := hδ.trans_le ht
  have hd : 2*Real.pi*|a| *δ ≤ ‖squareGaussianParameter ε a t‖ := by
    calc
      _ ≤ 2*Real.pi*|a| *t := mul_le_mul_of_nonneg_left ht (by positivity)
      _ = |(squareGaussianParameter ε a t).im| := by
        simp [squareGaussianParameter_im,abs_mul,abs_of_pos Real.pi_pos,abs_of_pos htpos]
      _ ≤ _ := Complex.abs_im_le_norm _
  have hdpos : 0<2*Real.pi*|a| *δ := by positivity
  unfold squareGaussianValue
  rw [show (1/2 : ℂ)=((1/2 : ℝ) : ℂ) by norm_num,Complex.norm_cpow_real,norm_div,
    Complex.norm_real,Real.norm_eq_abs,abs_of_pos Real.pi_pos]
  exact Real.rpow_le_rpow (by positivity)
    (div_le_div_of_nonneg_left Real.pi_pos.le hdpos hd) (by norm_num)

theorem squareGaussianValue_continuousAt_zero {a t : ℝ} (ha : a≠0) (ht : t≠0) :
    ContinuousAt (fun ε : ℝ => squareGaussianValue ε a t) 0 := by
  have hn := squareGaussianParameter_ne_zero ha ht 0
  have hz : 0 ≤ ((Real.pi : ℂ)/squareGaussianParameter 0 a t).re := by
    simp [Complex.div_re,squareGaussianParameter_re]
  have hratio : ContinuousAt (fun ε : ℝ => (Real.pi : ℂ)/squareGaussianParameter ε a t) 0 :=
    continuousAt_const.div (by unfold squareGaussianParameter; fun_prop) hn
  have hcp : ContinuousAt (fun z : ℂ => z^(1/2 : ℂ))
      ((fun ε : ℝ => (Real.pi : ℂ)/squareGaussianParameter ε a t) 0) :=
    Complex.continuousAt_cpow_const_of_re_pos (Or.inl hz) (by norm_num)
  exact ContinuousAt.comp (x := (0 : ℝ)) (f := fun ε : ℝ =>
    (Real.pi : ℂ)/squareGaussianParameter ε a t) hcp hratio

theorem tendsto_squareGaussianValue_integral (W : 𝓢(ℝ, ℂ)) {a δ : ℝ}
    (ha : a≠0) (hδ : 0<δ) (hW : ∀ t : ℝ, t<δ → W t=0) :
    Tendsto (fun ε : ℝ => ∫ t : ℝ, squareGaussianValue ε a t*W t) (𝓝[>] (0 : ℝ))
      (𝓝 (∫ t : ℝ, squareGaussianValue 0 a t*W t)) := by
  let C := (Real.pi/(2*Real.pi*|a| *δ))^(1/2 : ℝ)
  apply tendsto_integral_filter_of_dominated_convergence (fun t : ℝ => C*‖W t‖)
  · apply Filter.Eventually.of_forall
    intro ε
    apply Measurable.aestronglyMeasurable
    unfold squareGaussianValue squareGaussianParameter
    fun_prop
  · apply Filter.Eventually.of_forall
    intro ε
    filter_upwards with t
    by_cases ht : t<δ
    · simp [hW t ht]
    · rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (squareGaussianValue_bound ha hδ (le_of_not_gt ht) ε)
        (norm_nonneg _)
  · exact W.integrable.norm.const_mul C
  · filter_upwards with t
    by_cases ht : t<δ
    · simp only [hW t ht,mul_zero]
      exact tendsto_const_nhds
    · have htne : t≠0 := (hδ.trans_le (le_of_not_gt ht)).ne'
      exact ((squareGaussianValue_continuousAt_zero ha htne).mul continuousAt_const).tendsto.mono_left
        nhdsWithin_le_nhds

theorem fourier_square_integral_gaussian (W : 𝓢(ℝ, ℂ)) {a δ : ℝ}
    (ha : a≠0) (hδ : 0<δ) (hW : ∀ t : ℝ, t<δ → W t=0) :
    (∫ x : ℝ, (𝓕 W) (a*x^2)) = ∫ t : ℝ, squareGaussianValue 0 a t*W t := by
  have hleft := tendsto_damped_fourier_square_integral W ha
  have hright := tendsto_squareGaussianValue_integral W ha hδ hW
  have heq : (fun ε : ℝ => ∫ x : ℝ, (Real.exp (-ε*x^2) : ℂ)*(𝓕 W) (a*x^2))
      =ᶠ[𝓝[>] (0 : ℝ)] (fun ε : ℝ => ∫ t : ℝ, squareGaussianValue ε a t*W t) := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact damped_fourier_square_integral W hε a
  exact tendsto_nhds_unique (hleft.congr' heq) hright

end Ostmann.QuadraticSieve

end

end OAI
