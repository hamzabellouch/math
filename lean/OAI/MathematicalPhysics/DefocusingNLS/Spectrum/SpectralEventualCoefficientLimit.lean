import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralWeightedCoefficientLimit

namespace OAI

/-! Finite initial indices do not affect the weighted coefficient limit. -/

open Filter Topology
open scoped BoundedContinuousFunction
namespace DefocusingNLS

theorem exists_spectral_weighted_coefficient_limit_eventually
    (m : ℕ → ℕ) (hmTop : Tendsto m atTop atTop)
    (q p : ℕ → ℝ → ℂ) (hq : ∀ n, Continuous (q n)) (hp : ∀ n, Continuous (p n))
    (κ T ρ C : ℝ) (hρ : 0 < ρ) (hρ1 : ρ < 1) (hC : 0 ≤ C)
    (e : ℕ → ℝ →ᵇ ℂ)
    (he : ∀ᶠ n in atTop, 1 ≤ m n ∧ ‖e n‖ ≤ C ∧ ∀ t, T ≤ t →
      ‖q n t‖ ≤ ρ ∧ ‖p n t‖ ≤ ρ ∧
        q n t-p n t=(Real.exp (-κ*t) : ℂ)*e n t) :
    ∃ A B : ℕ → ℝ →ᵇ ℂ, Tendsto A atTop (𝓝 0) ∧ Tendsto B atTop (𝓝 0) ∧
      ∀ᶠ n in atTop, ∀ t, T ≤ t →
        A n t=(Real.exp (κ*t) : ℂ)*
          (spectralDiagonalCoefficient (m n) (q n t)-spectralDiagonalCoefficient (m n) (p n t)) ∧
        B n t=(Real.exp (κ*t) : ℂ)*
          (spectralCrossCoefficient (m n) (q n t)-spectralCrossCoefficient (m n) (p n t)) := by
  obtain ⟨N,hN⟩ := eventually_atTop.mp he
  have hs (n : ℕ) := hN (n+N) (by omega)
  obtain ⟨A,B,hA,hB,hAB⟩ := exists_spectral_weighted_coefficient_limit
    (fun n => m (n+N)) (fun n => (hs n).1) (hmTop.comp (tendsto_add_atTop_nat N))
    (fun n => q (n+N)) (fun n => p (n+N)) (fun n => hq (n+N)) (fun n => hp (n+N))
    κ T ρ C hρ hρ1 hC (fun n => e (n+N)) (fun n => (hs n).2.1)
    (fun n t ht => ((hs n).2.2 t ht).1)
    (fun n t ht => ((hs n).2.2 t ht).2.1)
    (fun n t ht => ((hs n).2.2 t ht).2.2)
  refine ⟨fun n => A (n-N),fun n => B (n-N),
    hA.comp (tendsto_sub_atTop_nat N),hB.comp (tendsto_sub_atTop_nat N),?_⟩
  filter_upwards [eventually_ge_atTop N] with n hn t ht
  simpa only [Nat.sub_add_cancel hn] using hAB (n-N) t ht

end DefocusingNLS

end OAI
