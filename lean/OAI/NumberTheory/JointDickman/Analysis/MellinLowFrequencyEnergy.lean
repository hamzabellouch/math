import OAI.NumberTheory.JointDickman.Amplification.BinLowFrequency

namespace OAI

/-! # The vanishing low-frequency energy of the actual centered bin labels -/
namespace JointDickman
open Finset Filter MeasureTheory
open scoped Topology

lemma angularMellinPolynomial_continuous (S : Finset ℕ) (a : ℕ → ℂ) :
    Continuous (angularMellinPolynomial S a) := by
  unfold angularMellinPolynomial
  fun_prop

lemma angularMellin_bounded_energy_le (S : Finset ℕ) (a : ℕ → ℂ)
    {T δ : ℝ} (hT : 0 ≤ T) (_hδ : 0 ≤ δ)
    (hbound : ∀ t : ℝ, |t| ≤ T → ‖angularMellinPolynomial S a t‖ ≤ δ) :
    (∫ t in -T..T, ‖angularMellinPolynomial S a t‖ ^ 2) ≤ 2*T*δ^2 := by
  have hi : IntervalIntegrable (fun t => ‖angularMellinPolynomial S a t‖^2) volume (-T) T :=
    ((angularMellinPolynomial_continuous S a).norm.pow 2).intervalIntegrable (-T) T
  have hh := intervalIntegral.integral_mono_on (by linarith : -T ≤ T) hi
    (intervalIntegrable_const (c := δ^2)) (fun t ht =>
      pow_le_pow_left₀ (norm_nonneg _) (hbound t (abs_le.mpr ht)) 2)
  simpa only [intervalIntegral.integral_const, smul_eq_mul, sub_neg_eq_add,
    ←two_mul] using hh

lemma angularMellin_bounded_energy_tendsto {ι : Type*} (l : Filter ι)
    (S : ι → Finset ℕ) (a : ι → ℕ → ℂ) {T : ℝ} (hT : 0 ≤ T)
    (hbound : ∀ δ : ℝ, 0 < δ → ∀ᶠ i in l, ∀ t : ℝ, |t| ≤ T →
      ‖angularMellinPolynomial (S i) (a i) t‖ ≤ δ) :
    Tendsto (fun i => ∫ t in -T..T, ‖angularMellinPolynomial (S i) (a i) t‖^2)
      l (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let δ := min 1 (ε/(2*(2*T+1)))
  have hden : 0 < 2*(2*T+1) := by positivity
  have hδ : 0 < δ := lt_min (by norm_num) (div_pos hε hden)
  have hδ1 : δ ≤ 1 := min_le_left _ _
  have hδeps : (2*T+1)*δ ≤ ε/2 := by
    have hh := (le_div_iff₀ hden).mp (min_le_right (1 : ℝ) (ε/(2*(2*T+1))))
    change δ * (2*(2*T+1)) ≤ ε at hh
    linarith
  filter_upwards [hbound δ hδ] with i hi
  have hnonneg : 0 ≤ ∫ t in -T..T, ‖angularMellinPolynomial (S i) (a i) t‖^2 :=
    intervalIntegral.integral_nonneg (by linarith) (fun _ _ => sq_nonneg _)
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hnonneg]
  have hb := angularMellin_bounded_energy_le (S i) (a i) hT hδ.le hi
  have hs : δ^2 ≤ δ := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_left hs (by positivity : 0 ≤ 2*T)]

/-- The low-frequency energy of the bin labels and finite-prime weights
tends to zero. -/
theorem weightedBin_low_frequency_energy {J : ℕ} (hJ : 2 ≤ J)
    (ζ : Fin (J-1) → ℂ) (hζ : ∀ i, ‖ζ i‖ ≤ 1) :
    ∃ μ : ℂ, ‖μ‖ ≤ 1 ∧ ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime) →
      ∀ t : ℕ → ℝ, (∀ p ∈ P, 0 ≤ t p ∧ t p ≤ 1) →
      ∀ A T : ℝ, 0 < A → 0 ≤ T →
      Tendsto (fun x : ℝ => ∫ τ in -T..T,
        ‖angularMellinPolynomial (Ioc ⌊A*x⌋₊ ⌊4*(A*x)⌋₊)
          (centeredWeightedBinCoefficient J ζ μ P t x) τ‖^2) atTop (𝓝 0) := by
  obtain ⟨μ, hμ, hlow⟩ := weightedBin_low_frequency hJ ζ hζ
  refine ⟨μ, hμ, ?_⟩
  intro P hP t ht A T hA hT
  apply angularMellin_bounded_energy_tendsto atTop _ _ hT
  intro δ hδ
  exact hlow P hP t ht A T δ hA hT hδ

end JointDickman

end OAI
