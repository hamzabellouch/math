import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingLocalizationEnergy
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadianFourierLocalization

namespace OAI

/-! # The exact homogeneous Fourier energy of a finite localized polynomial

The dilation identity supplies the factor L^(12-2s). The weighted mixed
estimate then controls both orders of Y by the exact Y_L coefficient norm.
-/

open MeasureTheory
open scoped SchwartzMap

namespace DefocusingNLS

local notation "E" => EuclideanSpace ℝ (Fin 12)

noncomputable def homogeneousFourierEnergy (s : ℝ) (f : E → ℂ) : ℝ :=
  ∫ ξ, ‖ξ‖ ^ (2 * s) * ‖radianFourierIntegral f ξ‖ ^ 2

private theorem homogeneousKernel_density_scale (s L : ℝ) (hL : 0 < L)
    (F : E → ℂ) (ξ : E) :
    ‖ξ‖ ^ (2 * s) * ‖(L ^ (12 : ℕ) : ℝ) • F (L • ξ)‖ ^ 2 =
      L ^ (24 - 2 * s) * (‖L • ξ‖ ^ (2 * s) * ‖F (L • ξ)‖ ^ 2) := by
  have hcoef : L ^ (24 - 2 * s) * L ^ (2 * s) = L ^ (24 : ℝ) := by
    rw [← Real.rpow_add hL]
    congr 1
    ring
  have hnat : (L ^ (12 : ℕ)) ^ 2 = L ^ (24 : ℝ) := by
    norm_num [← pow_mul]
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity), norm_smul,
    Real.norm_eq_abs, abs_of_pos hL, Real.mul_rpow hL.le (norm_nonneg ξ), mul_pow, hnat]
  calc
    _ = (L ^ (24 : ℝ) * ‖ξ‖ ^ (2 * s)) * ‖F (L • ξ)‖ ^ 2 := by ring
    _ = _ := by rw [← hcoef]; ring

private theorem homogeneousKernel_dilation (s L : ℝ) (hL : 0 < L) (F : E → ℂ) :
    (∫ ξ, ‖ξ‖ ^ (2 * s) * ‖(L ^ (12 : ℕ) : ℝ) • F (L • ξ)‖ ^ 2) =
      L ^ (12 - 2 * s) * ∫ ξ, ‖ξ‖ ^ (2 * s) * ‖F ξ‖ ^ 2 := by
  let H : E → ℝ := fun ξ => ‖ξ‖ ^ (2 * s) * ‖F ξ‖ ^ 2
  simp_rw [homogeneousKernel_density_scale s L hL F]
  rw [integral_const_mul, Measure.integral_comp_smul_of_nonneg
    (volume : Measure E) H L (hR := hL.le), finrank_euclideanSpace_fin]
  change L ^ (24 - 2 * s) * ((L ^ (12 : ℕ))⁻¹ * ∫ ξ, H ξ) = _
  have hscale : L ^ (24 - 2 * s) * (L ^ (12 : ℕ))⁻¹ = L ^ (12 - 2 * s) := by
    rw [← Real.rpow_natCast, ← Real.rpow_neg hL.le, ← Real.rpow_add hL]
    congr 1
    ring
  rw [← mul_assoc, hscale]

private theorem homogeneousKernel_bessel_control (s : ℝ) (hs : 0 ≤ s)
    (K : 𝓢(E, ℂ)) (S : Finset frequencyLattice) (v : frequencyLattice → ℂ) :
    Integrable (fun ξ => ‖ξ‖ ^ (2 * s) * ‖∑ n ∈ S, v n * K (ξ - n)‖ ^ 2) ∧
      (∫ ξ, ‖ξ‖ ^ (2 * s) * ‖∑ n ∈ S, v n * K (ξ - n)‖ ^ 2) ≤
        ∫ ξ, (1 + ‖ξ‖ ^ 2) ^ s * ‖∑ n ∈ S, v n * K (ξ - n)‖ ^ 2 := by
  have hweight (ξ : E) : ‖ξ‖ ^ (2 * s) ≤ (1 + ‖ξ‖ ^ 2) ^ s := by
    calc
      _ = (‖ξ‖ ^ 2) ^ s := by rw [← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg ξ)]; norm_num
      _ ≤ _ := Real.rpow_le_rpow (by positivity) (by linarith) hs
  obtain ⟨C, hC, hb⟩ := exists_schwartz_sobolev_localization_bound s hs K
  have hBI := (hb S v).1
  have hcont : Continuous (fun ξ : E => ‖ξ‖ ^ (2 * s) *
      ‖∑ n ∈ S, v n * K (ξ - n)‖ ^ 2) := by
    have hK : Continuous K := K.continuous
    have hpow : Continuous (fun ξ : E => ‖ξ‖ ^ (2 * s)) :=
      continuous_norm.rpow_const (fun _ => Or.inr (by positivity))
    fun_prop
  have hI : Integrable (fun ξ : E => ‖ξ‖ ^ (2 * s) *
      ‖∑ n ∈ S, v n * K (ξ - n)‖ ^ 2) := by
    apply hBI.mono' hcont.aestronglyMeasurable
    filter_upwards [] with ξ
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact mul_le_mul_of_nonneg_right (hweight ξ) (sq_nonneg _)
  exact ⟨hI, integral_mono hI hBI (fun ξ => mul_le_mul_of_nonneg_right (hweight ξ) (sq_nonneg _))⟩

/-- Each finite physical cutoff has finite homogeneous Fourier energy. -/
theorem integrable_localizedFourierPolynomial_energy (s L : ℝ) (hs : 0 ≤ s) (hL : 0 < L)
    (χ : 𝓢(E, ℂ)) (S : Finset frequencyLattice) (v : frequencyLattice → ℂ) :
    Integrable (fun ξ => ‖ξ‖ ^ (2 * s) *
      ‖radianFourierIntegral (localizedFourierPolynomial L χ S v) ξ‖ ^ 2) := by
  have h := (homogeneousKernel_bessel_control s hs (radianFourierKernel χ) S v).1
  have hc := (h.comp_smul hL.ne').const_mul (L ^ (24 - 2 * s))
  convert hc using 1
  funext ξ
  rw [localizedFourierPolynomial_transform L hL]
  exact homogeneousKernel_density_scale s L hL
    (fun x => ∑ n ∈ S, v n * radianFourierKernel χ (x - n)) ξ

/-- The finite Fourier version of the manuscript's uniform cutoff estimate.
The right side is the exact Y_L coefficient density, before the common (2π)^12 normalization. -/
theorem exists_localizedFourierPolynomial_energy_bound (a k : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (χ : 𝓢(E, ℂ)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (L : ℝ), 1 ≤ L →
      ∀ (S : Finset frequencyLattice) (v : frequencyLattice → ℂ),
      homogeneousFourierEnergy (6 - a) (localizedFourierPolynomial L χ S v) +
        homogeneousFourierEnergy k (localizedFourierPolynomial L χ S v) ≤
          C * ∑ n ∈ S, expandingSobolevWeightSq a k L n * ‖v n‖ ^ 2 := by
  obtain ⟨C, hC, hbound⟩ := exists_expanding_localization_energy_bound a k ha ha1 hk
    (radianFourierKernel χ)
  refine ⟨C, hC, ?_⟩
  intro L hL S v
  have hLp : 0 < L := by linarith
  have henergy (s : ℝ) (hs : 0 ≤ s) :
      homogeneousFourierEnergy s (localizedFourierPolynomial L χ S v) ≤
        L ^ (12 - 2 * s) * ∫ ξ, (1 + ‖ξ‖ ^ 2) ^ s *
          ‖∑ n ∈ S, v n * radianFourierKernel χ (ξ - n)‖ ^ 2 := by
    unfold homogeneousFourierEnergy
    simp_rw [localizedFourierPolynomial_transform L hLp]
    rw [homogeneousKernel_dilation s L hLp
      (fun ξ => ∑ n ∈ S, v n * radianFourierKernel χ (ξ - n))]
    exact mul_le_mul_of_nonneg_left
      (homogeneousKernel_bessel_control s hs (radianFourierKernel χ) S v).2 (by positivity)
  have hlo := henergy (6 - a) (by linarith)
  have hhi := henergy k (by linarith)
  have hexp : 12 - 2 * (6 - a) = 2 * a := by ring
  rw [hexp] at hlo
  exact (add_le_add hlo hhi).trans (hbound L hL S v)

end DefocusingNLS

end OAI
