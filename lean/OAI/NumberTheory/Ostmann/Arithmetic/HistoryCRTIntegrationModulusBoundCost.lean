import OAI.NumberTheory.Ostmann.Arithmetic.HistoryCRTIntegrationModulusBound

namespace OAI

open Erdos970

namespace Ostmann.Arithmetic.HistoryCRTIntegration

lemma crtCostCoefficient_mono {l k n m : ℕ} (hl : l ≤ k) (hn : n ≤ m) :
    crtCostCoefficient l n ≤ crtCostCoefficient k m := by
  have htwo : (2:ℕ)^(l+1) ≤ 2^(k+1) := Nat.pow_le_pow_right (by omega) (by omega)
  have hfour : (4:ℕ)^(l+1) ≤ 4^(k+1) := Nat.pow_le_pow_right (by omega) (by omega)
  have hfreq := Nat.mul_le_mul (Nat.mul_le_mul_left 2 htwo) hn
  have hrep := Nat.mul_le_mul_left 4 hfour
  unfold crtCostCoefficient
  omega

end Ostmann.Arithmetic.HistoryCRTIntegration

end OAI
