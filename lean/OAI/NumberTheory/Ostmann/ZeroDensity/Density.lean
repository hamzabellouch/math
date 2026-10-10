import OAI.NumberTheory.Ostmann.ZeroDensity.ActualDensityDyadic
import OAI.NumberTheory.Ostmann.ZeroDensity.DensityNumerics
import OAI.NumberTheory.Ostmann.ZeroDensity.MultiplicityLog

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
open scoped BigOperators
namespace Ostmann.ZeroDensity

theorem exists_actual_zero_density_constant :
    ∃ C : ℝ, 0 < C ∧ ∀ (Q H : ℕ) (exception : Option (PrimitiveFamily Q)) (σ : ℝ),
      0 < Q → 0 < H → 1/2 ≤ σ → σ ≤ 1 →
      (totalZeroCount Q exception σ (H : ℝ) : ℝ) ≤
        C*((Q^2*H : ℕ) : ℝ)^(10*(1-σ))*(1+Real.log (Q*H : ℕ))^11 := by
  obtain ⟨Cs,hCs,hs⟩ := exists_actual_zero_density_dyadic_constant
  obtain ⟨Cn,hCn,hn⟩ := exists_density_numerical_constant
  obtain ⟨Cm,hCm,hm⟩ := exists_localMultiplicity_log_constant
  refine ⟨2*Cs*Cn*Cm,by positivity,?_⟩
  intro Q H exception σ hQ hH hσ hσ1
  let J := detectorBlockCount (detectorLength Q H (Q^2*H))
  let E : ℝ := ∑ j ∈ Finset.range J,
    (((2^j*(Q^2*H) : ℕ) : ℝ)+(Q : ℝ)^2*H) * (1+Real.log Q) *
      (1+Real.log (2*(2^j*(Q^2*H) : ℕ) : ℝ))^7 *
        (2^j*(Q^2*H) : ℕ) * ((2^j*(Q^2*H) : ℕ) : ℝ)^(-2*σ)
  let L : ℝ := 1+Real.log (Q*H : ℕ)
  let Z : ℝ := ((Q^2*H : ℕ) : ℝ)^(10*(1-σ))
  have hL : 0 ≤ L := by
    have hp : 0 < Q*H := Nat.mul_pos hQ hH
    have hreal : (1 : ℝ) ≤ (Q*H : ℕ) := by exact_mod_cast hp
    have := Real.log_nonneg hreal
    dsimp [L]
    linarith
  have hZ : 0 ≤ Z := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hlocal := localMultiplicityBound_nonneg hQ (show (1 : ℝ) ≤ H by exact_mod_cast hH)
  have hactual : (totalZeroCount Q exception σ (H : ℝ) : ℝ) ≤
      8*Cs*localMultiplicityBound Q H*J*E := hs Q H exception σ hQ hH hσ hσ1
  have hnumeric : 4*(J : ℝ)*E ≤ Cn*Z*L^10 := hn Q H σ hQ hH (by linarith) hσ1
  have hmultiplicity : localMultiplicityBound Q H ≤ Cm*L := by
    simpa only [L,Nat.cast_mul] using hm Q H hQ hH
  calc
    (totalZeroCount Q exception σ (H : ℝ) : ℝ) ≤
        8*Cs*localMultiplicityBound Q H*J*E := hactual
    _ = (2*Cs*localMultiplicityBound Q H)*(4*(J : ℝ)*E) := by ring
    _ ≤ (2*Cs*localMultiplicityBound Q H)*(Cn*Z*L^10) :=
      mul_le_mul_of_nonneg_left hnumeric (by positivity)
    _ ≤ (2*Cs*(Cm*L))*(Cn*Z*L^10) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hmultiplicity (by positivity)) (by positivity)
    _ = (2*Cs*Cn*Cm)*Z*L^11 := by ring

end Ostmann.ZeroDensity

end

end OAI
