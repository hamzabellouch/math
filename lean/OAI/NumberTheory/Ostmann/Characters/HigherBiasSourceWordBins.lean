import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Data.Int.Interval
import OAI.NumberTheory.Ostmann.Characters.HigherBiasSourceWordDefs

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Characters.HigherBiasSourceWord

theorem bins_card_le {τ : ℝ} (hτ : 1≤τ) : ((bins τ).card:ℝ)≤5*τ := by
  have ht : τ≤(Real.exp 1+1)*τ := by nlinarith [Real.exp_pos (1:ℝ)]
  have ho : ⌊τ⌋≤⌊(Real.exp 1+1)*τ⌋+1 := by
    exact (Int.floor_mono ht).trans (by omega)
  have hc := Int.card_Icc_of_le ⌊τ⌋ ⌊(Real.exp 1+1)*τ⌋ ho
  have he : ((bins τ).card:ℝ)=((⌊(Real.exp 1+1)*τ⌋:ℤ):ℝ)+1-(⌊τ⌋:ℤ) := by
    exact_mod_cast hc
  rw [he]
  have hlo := Int.lt_floor_add_one τ
  have hhi := Int.floor_le ((Real.exp 1+1)*τ)
  nlinarith [Real.exp_one_lt_three]

theorem bins_location {τ : ℝ} (hτ : 10≤τ) {J : ℤ} (hJ : J∈bins τ) :
    (9/10:ℝ)*τ≤(J:ℝ) ∧ (J:ℝ)≤4*τ := by
  obtain ⟨hlo,hhi⟩ := Finset.mem_Icc.mp hJ
  have hlo' : ((⌊τ⌋:ℤ):ℝ)≤J := by exact_mod_cast hlo
  have hhi' : (J:ℝ)≤((⌊(Real.exp 1+1)*τ⌋:ℤ):ℝ) := by exact_mod_cast hhi
  have hflo := Int.lt_floor_add_one τ
  have hfhi := Int.floor_le ((Real.exp 1+1)*τ)
  constructor <;> nlinarith [Real.exp_one_lt_three]

end Ostmann.Characters.HigherBiasSourceWord

end

end OAI
