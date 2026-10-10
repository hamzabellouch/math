import OAI.MathematicalPhysics.Boltzmann.Branching.AverageFourierTail
import OAI.MathematicalPhysics.Boltzmann.Branching.BoundedMeshStep
import OAI.MathematicalPhysics.Boltzmann.Branching.ComplexWeakL2Diagonal
import OAI.MathematicalPhysics.Boltzmann.Collision.FourierCompactness
import OAI.MathematicalPhysics.Boltzmann.Compactness.PhysicalFrequencyWindow

namespace OAI

section

/-! # Uniform L2 Fourier tails on each bounded-source class -/
noncomputable section
open MeasureTheory Set
open scoped FourierTransform
namespace BoltzmannNonuniqueness.Published

theorem bounded_average_uniform_tails (R B C : ℝ) (hB : 0 ≤ B) (hC : 0 ≤ C)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ S : Set FourierSpace, ∃ hS : MeasurableSet S, volume S < ⊤ ∧
      ∀ (r : Velocity × FourierSpace → ℂ) (hr : Integrable r), Measurable r →
      ∀ (hb : ∀ p, ‖r p‖ ≤ B) (hs : ∀ p, R < ‖p.1‖ → r p = 0),
      (∫ p, ‖r p‖) ≤ C →
      let a := (velocityLineAverage_memLp_two hr hb hs).toLp (velocityLineAverage r)
      ‖(𝓕 a : Lp ℂ 2 volume)-complexL2Cutoff S hS (𝓕 a)‖ ≤ δ := by
  let ε := δ^2/(B*C+1)
  have hden : 0 < B*C+1 := by positivity
  have hε : 0 < ε := by dsimp [ε]; positivity
  obtain ⟨N,-,hN⟩ := average_fourier_tail (R := R) hε
  let S : Set FourierSpace := {k | ‖physicalFourierFrequency k‖ < N}
  have hS : MeasurableSet S :=
    measurableSet_lt physicalFourierFrequency_continuous.norm.measurable measurable_const
  have hfS : volume S < ⊤ := lt_of_le_of_lt
    (measure_mono (fun k hk => show ‖physicalFourierFrequency k‖ ≤ (N:ℝ) from le_of_lt hk))
    (physicalFrequencyWindow_finite N)
  refine ⟨S,hS,hfS,?_⟩
  intro r hr hm hb hs hmass a
  have h₂ := integrable_bounded_memLp_two hr hb
  have ha := velocityLineAverage_memLp_two hr hb hs
  have he := hN r hm hr h₂ ha (Filter.Eventually.of_forall hs)
  have herr : ‖(𝓕 a : Lp ℂ 2 volume)-complexL2Cutoff S hS (𝓕 a)‖^2 ≤ δ^2 := by
    rw [complexL2Cutoff_error]
    calc
      _ = ∫ k in Sᶜ, ‖𝓕 (velocityLineAverage r) k‖^2 := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_of_ae (fourier_L2_ae_eq_integral
          (velocityLineAverage_integrable hr) ha)] with k hk
        rw [hk]
      _ ≤ ε * ∫ p, ‖r p‖^2 := by simpa only [S,compl_ofPred,not_lt] using he
      _ ≤ ε*(B*C) := by
        apply mul_le_mul_of_nonneg_left _ hε.le
        exact (bounded_integrable_square_le hr hb).trans
          (mul_le_mul_of_nonneg_left hmass hB)
      _ ≤ ε*(B*C+1) := mul_le_mul_of_nonneg_left (by linarith) hε.le
      _ = δ^2 := by dsimp [ε]; field_simp
  nlinarith [norm_nonneg ((𝓕 a : Lp ℂ 2 volume)-complexL2Cutoff S hS (𝓕 a))]

end BoltzmannNonuniqueness.Published

end

end

section

/-! # Actual bounded-source averages are sequentially compact in local L2 -/
noncomputable section
open MeasureTheory Filter Set FourierTransform
open scoped Topology
namespace BoltzmannNonuniqueness.Published

def boundedAverageL2 {R B : ℝ} (r : Velocity × FourierSpace → ℂ) (hr : Integrable r)
    (hb : ∀ p, ‖r p‖ ≤ B) (hs : ∀ p, R < ‖p.1‖ → r p = 0) :
    Lp ℂ 2 (volume : Measure FourierSpace) :=
  (velocityLineAverage_memLp_two hr hb hs).toLp (velocityLineAverage r)

theorem bounded_average_compactness (r : ℕ → Velocity × FourierSpace → ℂ)
    (hm : ∀ n, Measurable (r n)) (hi : ∀ n, Integrable (r n))
    {R B C : ℝ} (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hb : ∀ n p, ‖r n p‖ ≤ B) (hs : ∀ n p, R < ‖p.1‖ → r n p = 0)
    (hbound : ∀ n, (∫ p, ‖r n p‖) ≤ C) :
    ∃ (φ : ℕ → ℕ) (g : Lp ℂ 2 (volume : Measure FourierSpace)), StrictMono φ ∧
      ∀ K : Set FourierSpace, volume K < ⊤ →
        Tendsto (fun n => ‖complexL2Restriction K
          (boundedAverageL2 (r (φ n)) (hi (φ n)) (hb (φ n)) (hs (φ n))-g)‖)
          atTop (𝓝 0) := by
  let a n := boundedAverageL2 (r n) (hi n) (hb n) (hs n)
  let u n : Lp ℂ 2 (volume : Measure FourierSpace) := 𝓕 (a n)
  let D := volume.real (Metric.closedBall (0 : Velocity) R)*B*C+1
  have ha n : ‖a n‖ ≤ D := bounded_average_L2_norm (hi n) hB (hb n) (hs n) (hbound n)
  have hu n : ‖u n‖ ≤ D := by simpa only [u,Lp.norm_fourier_eq] using ha n
  obtain ⟨φ,g,hφ,hg,hw⟩ := exists_weak_complex_L2_subsequence u D hu
  refine ⟨φ,𝓕⁻ g,hφ,?_⟩
  intro K hK
  have hD : 0 ≤ D := (norm_nonneg (u 0)).trans (hu 0)
  have ht : ∀ ε : ℝ, 0 < ε → ∃ S : Set FourierSpace, ∃ hS : MeasurableSet S,
      volume S < ⊤ ∧ ∀ n, ‖u (φ n)-complexL2Cutoff S hS (u (φ n))‖ ≤ ε := by
    intro ε hε
    obtain ⟨S,hS,hfinite,h⟩ := bounded_average_uniform_tails R B C hB hC hε
    refine ⟨S,hS,hfinite,fun n => ?_⟩
    exact h (r (φ n)) (hi (φ n)) (hm (φ n)) (hb (φ n)) (hs (φ n)) (hbound (φ n))
  have h := inverseFourier_local_strong_of_weak_and_tails hD (fun n => hu (φ n)) hg hw ht K hK
  simpa only [u,fourierInv_fourier_eq] using h

end BoltzmannNonuniqueness.Published

end

end

end OAI
