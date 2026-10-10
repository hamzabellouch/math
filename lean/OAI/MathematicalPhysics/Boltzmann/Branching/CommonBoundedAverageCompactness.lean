import OAI.MathematicalPhysics.Boltzmann.Branching.BoundedAverageCompactness
import OAI.MathematicalPhysics.Boltzmann.Branching.ComplexWeakL2Diagonal

namespace OAI

/-! # One subsequence for all bounded value truncations -/
noncomputable section
open MeasureTheory Filter Set FourierTransform
open scoped Topology
namespace BoltzmannNonuniqueness.Published

theorem common_bounded_average_compactness (r : ℕ → ℕ → Velocity × FourierSpace → ℂ)
    (hm : ∀ m n, Measurable (r m n)) (hi : ∀ m n, Integrable (r m n))
    (R : ℝ) (B C : ℕ → ℝ) (hB : ∀ m, 0 ≤ B m) (hC : ∀ m, 0 ≤ C m)
    (hb : ∀ m n p, ‖r m n p‖ ≤ B m)
    (hs : ∀ m n p, R < ‖p.1‖ → r m n p = 0)
    (hbound : ∀ m n, (∫ p, ‖r m n p‖) ≤ C m) :
    ∃ (φ : ℕ → ℕ) (g : ℕ → Lp ℂ 2 (volume : Measure FourierSpace)), StrictMono φ ∧
      ∀ m (K : Set FourierSpace), volume K < ⊤ →
        Tendsto (fun n => ‖complexL2Restriction K
          (boundedAverageL2 (r m (φ n)) (hi m (φ n)) (hb m (φ n)) (hs m (φ n))-g m)‖)
          atTop (𝓝 0) := by
  let a m n := boundedAverageL2 (r m n) (hi m n) (hb m n) (hs m n)
  let u m n : Lp ℂ 2 (volume : Measure FourierSpace) := 𝓕 (a m n)
  let D m := volume.real (Metric.closedBall (0 : Velocity) R)*B m*C m+1
  have ha m n : ‖a m n‖ ≤ D m :=
    bounded_average_L2_norm (hi m n) (hB m) (hb m n) (hs m n) (hbound m n)
  have hu m n : ‖u m n‖ ≤ D m := by simpa only [u,Lp.norm_fourier_eq] using ha m n
  obtain ⟨φ,g,hφ,hg⟩ := exists_common_weak_complex_L2_subsequence u D hu
  refine ⟨φ,fun m => 𝓕⁻ (g m),hφ,?_⟩
  intro m K hK
  have hD : 0 ≤ D m := (norm_nonneg (u m 0)).trans (hu m 0)
  have ht : ∀ ε : ℝ, 0 < ε → ∃ S : Set FourierSpace, ∃ hS : MeasurableSet S,
      volume S < ⊤ ∧ ∀ n, ‖u m (φ n)-complexL2Cutoff S hS (u m (φ n))‖ ≤ ε := by
    intro ε hε
    obtain ⟨S,hS,hfinite,h⟩ := bounded_average_uniform_tails R (B m) (C m) (hB m) (hC m) hε
    exact ⟨S,hS,hfinite,fun n =>
      h (r m (φ n)) (hi m (φ n)) (hm m (φ n)) (hb m (φ n)) (hs m (φ n)) (hbound m (φ n))⟩
  have h := inverseFourier_local_strong_of_weak_and_tails hD (fun n => hu m (φ n))
    (hg m).1 (hg m).2 ht K hK
  simpa only [u,fourierInv_fourier_eq] using h

end BoltzmannNonuniqueness.Published

end

end OAI
