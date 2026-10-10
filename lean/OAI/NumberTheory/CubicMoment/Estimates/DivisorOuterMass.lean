import OAI.NumberTheory.CubicMoment.Estimates.AllFrequencyOuterSieve
import OAI.NumberTheory.CubicMoment.Estimates.PrimeDivisorMassBound

namespace OAI

/-! Apply the outer cubic sieve to the literal shortened Poisson rows,
uniformly in the two Mellin signs. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem fullPrime_divisor_outer_mass {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (R : ℝ) (W : ι → ℝ → ℂ) (X : ι → ℝ)
      (f e : Eisenstein) (H : Finset Eisenstein) (u t N₀ B N : ℝ),
      (∀ i, 0 < X i) → (∀ i x, x < 1 → W i x = 0) →
      (∀ i x, R < x → W i x = 0) → primary f → 0 < N₀ →
      1 ≤ B → 1 ≤ N →
      (∀ n ∈ fullPrimeSliceSupport R W X f e, norm n ≤ N) →
      (∀ h ∈ H, h ≠ 0 ∧ norm h ≤ B) →
      fullPrimeDivisorMellinMass R W X e H u N₀ f t ≤
        C*(2*B*N)^ε*(B+(B*N)^(2/3:ℝ)+B^(1/3:ℝ)*N)*
          ∑ n ∈ fullPrimeSliceSupport R W X f e, ‖fullPrimeCoefficient R W X (f*n)‖^2 := by
  obtain ⟨C,hC,houter⟩ := all_frequency_outer_sieve hε
  refine ⟨C,hC,?_⟩
  intro R W X f e H u t N₀ B N hX hlo hhi hf hN₀ hB hN hS hH
  have hbound (v : ℝ) :
      (∑ h ∈ H, ‖fullPrimeSliceSum R W X f e h 1 0 v‖^2) ≤
        C*(2*B*N)^ε*(B+(B*N)^(2/3:ℝ)+B^(1/3:ℝ)*N)*
          ∑ n ∈ fullPrimeSliceSupport R W X f e, ‖fullPrimeCoefficient R W X (f*n)‖^2 := by
    let β := fun n => fullPrimeCoefficient R W X (f*n)*mellinPhase v (norm n)
    have hp : ∀ n ∈ fullPrimeSliceSupport R W X f e,
        primary n ∧ Squarefree n ∧ norm n ≤ N := by
      intro n hn
      have hh := fullPrimeSliceSupport_bounds R W X f e hn
      exact ⟨hh.1,hh.2.1,hS n hn⟩
    have hh := houter (fullPrimeSliceSupport R W X f e) H B N hB hN hp hH β
    simpa only [fullPrimeSliceSum,theta_zero,mul_one,one_mul,β,norm_mul,
      mellinPhase_norm] using hh
  apply (fullPrimeDivisorMellinMass_le W X hX hlo hhi hf e H u t hN₀).trans
  have hp := hbound (u+2*Real.pi*t)
  have hn := hbound (u-2*Real.pi*t)
  linarith

end CubicFirstMoment

end

end OAI
