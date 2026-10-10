import OAI.NumberTheory.Ostmann.Supply.PrimePowerTransfer
import OAI.NumberTheory.Ostmann.ZeroDensity.ContourPolynomial

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
open Filter Set
open scoped Topology
namespace Ostmann.ZeroDensity

theorem eventually_supply_prime_power_decay {C : ℝ} (hC : 0 < C) (D : ℝ) :
    ∀ᶠ L : ℝ in atTop, ∀ Q : ℕ, 0 < Q → Q ≤ supplyConductorCutoff L →
      (Q : ℝ)^2*C*Real.sqrt (supplyPrimeSample L : ℝ) ≤
        (supplyPrimeSample L : ℝ)*Real.exp (-D*L) := by
  have hl := eventually_supply_left_edge_decay 0 0 (E := 0) (by norm_num) (D+1)
  have hc := eventually_constant_exp_decay hC D
  filter_upwards [hl,hc] with L hl hc
  intro Q hQ hQQ
  have hh := hl Q hQ hQQ
  simp only [pow_zero,mul_one] at hh
  calc
    _ = C*((Q : ℝ)^2*Real.sqrt (supplyPrimeSample L : ℝ)) := by ring
    _ ≤ C*((supplyPrimeSample L : ℝ)*Real.exp (-(D+1)*L)) :=
      mul_le_mul_of_nonneg_left hh hC.le
    _ = (supplyPrimeSample L : ℝ)*(C*Real.exp (-(D+1)*L)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hc (Nat.cast_nonneg _)

theorem prime_error_supply_decay_of_vonMangoldt {φ : ℝ → ℝ}
    (hφ : Continuous φ) (hs : tsupport φ ⊆ Ioo (1/2 : ℝ) 1)
    (hΛ : ∀ D : ℝ, ∀ᶠ L : ℝ in atTop, ∀ Q : ℕ,
      0 < Q → Q ≤ supplyConductorCutoff L →
      totalPrimitiveError Q none φ (supplyPrimeSample L : ℝ) ≤
        (supplyPrimeSample L : ℝ)*Real.exp (-D*L)) (D : ℝ) :
    ∀ᶠ L : ℝ in atTop, ∀ Q : ℕ, 0 < Q → Q ≤ supplyConductorCutoff L →
      Ostmann.Supply.totalPrimitivePrimeError Q none φ (supplyPrimeSample L : ℝ) ≤
        (supplyPrimeSample L : ℝ)*Real.exp (-D*L) := by
  obtain ⟨C,hC,htransfer⟩ := Ostmann.Supply.exists_totalPrimitivePrimeError_le φ hφ hs
  have hpower := eventually_supply_prime_power_decay hC (D+1)
  have htwo := eventually_constant_exp_decay (C := 2) (by norm_num) D
  filter_upwards [hΛ (D+1),hpower,htwo] with L hmain hp htwo
  intro Q hQ hQQ
  have htr := htransfer Q none (supplyPrimeSample L : ℝ)
    (Nat.cast_pos.mpr (supplyPrimeSample_pos L))
  have hm := hmain Q hQ hQQ
  have hh := hp Q hQ hQQ
  have hb := mul_le_mul_of_nonneg_left htwo
    (Nat.cast_nonneg (supplyPrimeSample L) : (0 : ℝ) ≤ supplyPrimeSample L)
  linarith

end Ostmann.ZeroDensity

end

end OAI
