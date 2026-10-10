import OAI.NumberTheory.Ostmann.Characters.HeldCycleAverage
import OAI.NumberTheory.Ostmann.Characters.QuartetLocalBounds

namespace OAI

/-! # Applying the uniform quartet majorants to a nonempty signed cycle -/

namespace Ostmann

open scoped BigOperators

noncomputable local instance quartetCycleMeanFintype {p : ℕ} [Fact p.Prime] :
    Fintype (MulChar (ZMod p) ℂ) := Fintype.ofFinite _

noncomputable local instance quartetCycleMeanDecidableEq {p : ℕ} :
    DecidableEq (MulChar (ZMod p) ℂ) := Classical.decEq _

theorem quartetLocalMeanError_nonneg (p : ℕ) [Fact p.Prime] (ε : ℝ) :
    0 ≤ quartetLocalMeanError p ε := by
  apply add_nonneg (by positivity)
  exact mul_nonneg (by positivity)
    (add_nonneg (friendlyQuartetError_nonneg p ε) (twoBadQuartetError_nonneg p ε))

theorem quartet_cycle_majorant_mean_le {p : ℕ} [Fact p.Prime]
    {I : Type*} [Fintype I] [DecidableEq I]
    (g : ZMod p → ℂ) (hg : g 0 = 0)
    (henergy : (∑ x : ZMod p, ‖g x‖ ^ 2) ≤ (p : ℝ))
    (ε : ℝ) (hε : 0 ≤ ε) (hflat : MixedFourierBound g ε)
    (cL cR : I → Bool) (choice : I → QuartetMovingCase)
    (sign : I → ℤ) (i : I) (hi : sign i = 1 ∨ sign i = -1) :
    ((Fintype.card (ZMod p)ˣ : ℝ) ^ Fintype.card I)⁻¹ *
      (∑ y : I → (ZMod p)ˣ, ∑ ρ : I → MulChar (ZMod p) ℂ,
        if (∏ j : I, (ρ j) ^ sign j) = 1 then
          ∏ j : I, quartetMovingMajorant g (cL j) (cR j) (choice j) (ρ j) (y j) else 0) ≤
      quartetLocalMeanError p ε *
        (8 * ((p : ℝ) / (Fintype.card (ZMod p)ˣ : ℝ)) ^ 4) ^ (Fintype.card I - 1) := by
  have h := cycle_majorant_average_le
    (fun j ρ (y : (ZMod p)ˣ) => quartetMovingMajorant g (cL j) (cR j) (choice j) ρ y)
    sign i hi (quartetLocalMeanError p ε)
    (fun _ => 8 * ((p : ℝ) / (Fintype.card (ZMod p)ˣ : ℝ)) ^ 4)
    (quartetLocalMeanError_nonneg p ε)
    (fun j ρ y => quartetMovingMajorant_nonneg g (cL j) (cR j) (choice j) ρ y)
    (fun ρ => by
      simpa only [div_eq_mul_inv, mul_comm] using
        quartetMovingMajorant_mean_le g hg henergy ε hε hflat (cL i) (cR i) (choice i) ρ)
    (fun j => by
      simpa only [div_eq_mul_inv, mul_comm] using
        quartetMovingMajorant_total_mean_le g hg henergy (cL j) (cR j) (choice j))
  have hc : Fintype.card {j : I // j ≠ i} = Fintype.card I - 1 := by
    simpa only [Fintype.card_subtype_eq] using Fintype.card_subtype_compl (fun j : I => j = i)
  simpa only [Finset.prod_const, Finset.card_univ, hc] using h

end Ostmann

end OAI
