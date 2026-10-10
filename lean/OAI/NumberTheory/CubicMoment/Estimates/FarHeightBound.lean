import OAI.NumberTheory.CubicMoment.Estimates.FarMellinKernel
import OAI.NumberTheory.CubicMoment.Estimates.UniformHeightMellin

namespace OAI

/-! Uniform height means pass through the far-cutoff Mellin integral.
All frequency shifts are retained and the constant is independent of J. -/
noncomputable section
open MeasureTheory Filter
open scoped BigOperators FourierTransform
namespace CubicFirstMoment

lemma continuous_indexed_norm_polynomial {ι : Type*} (S : Finset ι) (c : ι → ℂ)
    (n : ι → Eisenstein) :
    Continuous (fun t : ℝ => ∑ a ∈ S, c a*normTwist t (n a)) :=
  continuous_finsetSum S (fun a _ => continuous_const.mul (continuous_normTwist (n a)))

lemma norm_indexed_norm_polynomial {ι : Type*} (S : Finset ι) (c : ι → ℂ)
    (n : ι → Eisenstein) (t : ℝ) :
    ‖∑ a ∈ S, c a*normTwist t (n a)‖ ≤ ∑ a ∈ S, ‖c a‖ := by
  simpa only [norm_mul,norm_normTwist,mul_one] using
    norm_sum_le S (fun a => c a*normTwist t (n a))

lemma far_norm_sum_norm_bound {ι : Type*} (S : Finset ι) (c : ι → ℂ)
    (n : ι → Eisenstein) (s x₀ : ℝ) {J : ℝ} (hJ : 0 < J) :
    ‖∑ a ∈ S, c a*normTwist s (n a)*
      farInverseSquare (J*(Real.log (norm (n a))-x₀))‖ ≤
      ∫ v : ℝ, ‖farMellinKernel J v‖*‖∑ a ∈ S, c a*normTwist (s+v) (n a)‖ := by
  rw [far_norm_sum_mellin S c n s x₀ hJ]
  apply (norm_integral_le_integral_norm _).trans_eq
  apply integral_congr_ae
  filter_upwards with v
  simp only [norm_mul]
  have hn : ‖Complex.exp ((-v*x₀:ℝ)*Complex.I)‖ = 1 := by simp [Complex.norm_exp]
  rw [hn,mul_one]

theorem far_norm_sum_height_bound {ι : Type*} (S : Finset ι) (c : ι → ℂ)
    (n : ι → Eisenstein) (s x₀ : ℝ) {J T B : ℝ} (hJ : 0 < J) (hT : 0 < T)
    (hmean : ∀ v : ℝ, dyadicHeightMean
      (fun t => ‖∑ a ∈ S, c a*normTwist (t+v) (n a)‖) T ≤ B) :
    dyadicHeightMean (fun t => ‖∑ a ∈ S, c a*normTwist (s+t) (n a)*
      farInverseSquare (J*(Real.log (norm (n a))-x₀))‖) T ≤
      B*(∫ u : ℝ, ‖𝓕 farInverseSquare u‖) := by
  let f := fun v : ℝ => ‖farMellinKernel J v‖
  let G := fun t : ℝ => ‖∑ a ∈ S, c a*normTwist t (n a)‖
  have hf : Continuous f := (farMellinKernel_continuous hJ).norm
  have hfi : Integrable f := (farMellinKernel_integrable hJ).norm
  have hG : Continuous G := (continuous_indexed_norm_polynomial S c n).norm
  have hGb : ∀ t : ℝ, ‖G t‖ ≤ ∑ a ∈ S, ‖c a‖ := by
    intro t
    simpa only [G,norm_norm] using norm_indexed_norm_polynomial S c n t
  have hc := continuous_height_convolution hf hfi hG hGb s
  have hs : Continuous (fun t : ℝ => ‖∑ a ∈ S, c a*normTwist (s+t) (n a)*
      farInverseSquare (J*(Real.log (norm (n a))-x₀))‖) := by
    apply Continuous.norm
    apply continuous_finsetSum
    intro a ha
    exact (continuous_const.mul ((continuous_normTwist (n a)).comp
      (continuous_const.add continuous_id))).mul continuous_const
  have hb := dyadicHeightMean_mono hs hc hT (fun t _ => by
    simpa only [f,G,add_comm s t] using far_norm_sum_norm_bound S c n (s+t) x₀ hJ)
  have ht := dyadicHeightMean_convolution_uniform hf hfi (fun _ => _root_.norm_nonneg _)
    hG hGb hT hmean s
  exact (hb.trans ht).trans_eq (by rw [show (∫ v : ℝ, f v) = _ from farMellinKernel_mass hJ])

/-- Specialization to one coefficient at each Eisenstein integer. -/
theorem far_gauss_sum_height_bound (S : Finset Eisenstein) (c : Eisenstein → ℂ)
    (s x₀ : ℝ) {J T B : ℝ} (hJ : 0 < J) (hT : 0 < T)
    (hmean : ∀ v : ℝ, dyadicHeightMean
      (fun t => ‖∑ a ∈ S, c a*normTwist (t+v) a‖) T ≤ B) :
    dyadicHeightMean (fun t => ‖∑ a ∈ S, c a*normTwist (s+t) a*
      farInverseSquare (J*(Real.log (norm a)-x₀))‖) T ≤
      B*(∫ u : ℝ, ‖𝓕 farInverseSquare u‖) :=
  far_norm_sum_height_bound S c id s x₀ hJ hT hmean

end CubicFirstMoment

end

end OAI
