import OAI.Dynamics.EntropyCounterexample.MapOrbitLift
import OAI.Dynamics.EntropyCounterexample.GlobalEscape

namespace OAI

noncomputable section

open Filter Set
open scoped Topology OnePoint

namespace Problem340.Construction

local instance : Fact ((0 : ℝ) < 100) := ⟨by norm_num⟩

lemma exists_period_representative (t : ℝ) :
    ∃ k : ℤ, t - 100 * (k : ℝ) ∈ Set.Ico (0 : ℝ) 100 := by
  refine ⟨⌊t / 100⌋, ?_⟩
  have hlo := Int.floor_le (t / 100)
  have hhi := Int.lt_floor_add_one (t / 100)
  constructor <;> linarith

theorem rawOrbit_main_square_of_no_readout (D : SphereData)
    (x : RawManifold) (t₀ : ℝ)
    (h₀ : (t₀ : AddCircle (100 : ℝ)) = x.1) (n : ℕ)
    (hquiet : ∀ k : ℤ, ¬ (100 * (k : ℝ) + 74 < rawClockLift D x t₀ n ∧
      rawClockLift D x t₀ n < 100 * (k : ℝ) + 80)) :
    ((rawMap D)^[n + 1] x).2.1 = perturbedSquare 0 (((rawMap D)^[n] x).2.1) := by
  obtain ⟨k, hk⟩ := exists_period_representative (rawClockLift D x t₀ n)
  have hcoeff : ∀ i : Fin 3,
      readoutCoeff i (rawClockLift D x t₀ n - 100 * (k : ℝ)) = 0 := by
    intro i
    by_contra h
    have hs : rawClockLift D x t₀ n - 100 * (k : ℝ) ∈
        Function.support (readoutCoeff i) := h
    rw [readoutCoeff_support] at hs
    have hwindow := readoutInterval_subset i hs
    exact hquiet k ⟨by linarith [hwindow.1], by linarith [hwindow.2]⟩
  simpa only [hcoeff, Complex.ofReal_zero, zero_mul, Finset.sum_const_zero, mul_zero]
    using main_update_at_passage_clock D x t₀ h₀ k n hk

theorem rawOrbit_norm_square_of_no_readout (D : SphereData)
    (x : RawManifold) (t₀ : ℝ)
    (h₀ : (t₀ : AddCircle (100 : ℝ)) = x.1)
    (z : ℕ → ℂ) (hz : ∀ n, (z n : Sphere) = ((rawMap D)^[n] x).2.1)
    (n : ℕ)
    (hquiet : ∀ k : ℤ, ¬ (100 * (k : ℝ) + 74 < rawClockLift D x t₀ n ∧
      rawClockLift D x t₀ n < 100 * (k : ℝ) + 80)) :
    ‖z (n + 1)‖ = ‖z n‖ ^ 2 := by
  have heq := rawOrbit_main_square_of_no_readout D x t₀ h₀ n hquiet
  rw [← hz (n + 1), ← hz n, perturbedSquare_coe, add_zero] at heq
  have hzsq : z (n + 1) = z n ^ 2 := OnePoint.coe_injective heq
  rw [hzsq, norm_pow]

theorem rawOrbit_norm_tendsto_atTop_of_passage_bounds (D : SphereData)
    (hgate : ∀ w, D.gate w ∈ Set.Icc (0 : ℝ) 1)
    (x : RawManifold) (t₀ : ℝ)
    (h₀ : (t₀ : AddCircle (100 : ℝ)) = x.1)
    (z : ℕ → ℂ) (hz : ∀ n, (z n : Sphere) = ((rawMap D)^[n] x).2.1)
    (hpass : ∀ k : ℤ, t₀ < 100 * (k : ℝ) →
      ∃ s hi : ℕ, rawClockLift D x t₀ s < 100 * (k : ℝ) + 74 ∧
        100 * (k : ℝ) + 80 ≤ rawClockLift D x t₀ hi ∧
        ∀ n, s ≤ n → n < hi → ‖z n‖ ^ 2 ≤ ‖z (n + 1)‖)
    (hlarge : ∃ k₀ : ℤ, ∃ N : ℕ, t₀ < 100 * (k₀ : ℝ) ∧
      100 * (k₀ : ℝ) ≤ rawClockLift D x t₀ N ∧ 1 < ‖z N‖) :
    Tendsto (fun n => ‖z n‖) atTop atTop := by
  apply GlobalEscape.tendsto_atTop_of_passage_bounds
    (rawClockLift D x t₀) (fun n => ‖z n‖)
    (monotone_rawClockLift D hgate x t₀) (fun n => norm_nonneg (z n))
  · intro n hn
    exact (rawOrbit_norm_square_of_no_readout D x t₀ h₀ z hz n hn).ge
  · simpa only [rawClockLift_zero] using hpass
  · simpa only [rawClockLift_zero] using hlarge

theorem rawOrbit_main_tendsto_infty_of_norm (D : SphereData)
    (x : RawManifold) (z : ℕ → ℂ)
    (hz : ∀ n, (z n : Sphere) = ((rawMap D)^[n] x).2.1)
    (hescape : Tendsto (fun n => ‖z n‖) atTop atTop) :
    Tendsto (fun n => ((rawMap D)^[n] x).2.1) atTop (𝓝 (∞ : Sphere)) := by
  exact (GlobalEscape.tendsto_coe_infty_of_norm hescape).congr hz

theorem rawOrbit_norm_tendsto_atTop_of_complete_passages (D : SphereData)
    (hgate : ∀ w, D.gate w ∈ Set.Icc (0 : ℝ) 1)
    (x : RawManifold) (t₀ : ℝ)
    (h₀ : (t₀ : AddCircle (100 : ℝ)) = x.1)
    (z : ℕ → ℂ) (hz : ∀ n, (z n : Sphere) = ((rawMap D)^[n] x).2.1)
    (hpass : ∀ k : ℤ, t₀ < 100 * (k : ℝ) →
      ∃ s hi : ℕ, 100 * (k : ℝ) ≤ rawClockLift D x t₀ s ∧
        rawClockLift D x t₀ s < 100 * (k : ℝ) + 74 ∧
        100 * (k : ℝ) + 80 ≤ rawClockLift D x t₀ hi ∧
        (∀ n, s ≤ n → n < hi → ‖z n‖ ^ 2 ≤ ‖z (n + 1)‖) ∧
        ∃ j, s ≤ j ∧ j ≤ hi ∧ 1 < ‖z j‖) :
    Tendsto (fun n => ‖z n‖) atTop atTop := by
  apply GlobalEscape.tendsto_atTop_of_complete_passages
    (rawClockLift D x t₀) (fun n => ‖z n‖)
    (monotone_rawClockLift D hgate x t₀) (fun n => norm_nonneg (z n))
  · intro n hn
    exact (rawOrbit_norm_square_of_no_readout D x t₀ h₀ z hz n hn).ge
  · simpa only [rawClockLift_zero] using hpass

theorem rawOrbit_main_tendsto_infty_of_complete_passages (D : SphereData)
    (hgate : ∀ w, D.gate w ∈ Set.Icc (0 : ℝ) 1)
    (x : RawManifold) (t₀ : ℝ)
    (h₀ : (t₀ : AddCircle (100 : ℝ)) = x.1)
    (z : ℕ → ℂ) (hz : ∀ n, (z n : Sphere) = ((rawMap D)^[n] x).2.1)
    (hpass : ∀ k : ℤ, t₀ < 100 * (k : ℝ) →
      ∃ s hi : ℕ, 100 * (k : ℝ) ≤ rawClockLift D x t₀ s ∧
        rawClockLift D x t₀ s < 100 * (k : ℝ) + 74 ∧
        100 * (k : ℝ) + 80 ≤ rawClockLift D x t₀ hi ∧
        (∀ n, s ≤ n → n < hi → ‖z n‖ ^ 2 ≤ ‖z (n + 1)‖) ∧
        ∃ j, s ≤ j ∧ j ≤ hi ∧ 1 < ‖z j‖) :
    Tendsto (fun n => ((rawMap D)^[n] x).2.1) atTop (𝓝 (∞ : Sphere)) := by
  exact rawOrbit_main_tendsto_infty_of_norm D x z hz
    (rawOrbit_norm_tendsto_atTop_of_complete_passages D hgate x t₀ h₀ z hz hpass)

end Problem340.Construction

end

end OAI
