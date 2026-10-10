import OAI.NumberTheory.CubicMoment.Angular.AngularStoppedCharacterRows
import OAI.NumberTheory.CubicMoment.Angular.AngularStoppedMellinRows
import OAI.NumberTheory.CubicMoment.Decomposition.StoppedDivisorRows
import OAI.NumberTheory.CubicMoment.Decomposition.StoppedMellinRows

namespace OAI

/-! Exact shortening for a divisor-restricted stopped row. The shortened
coefficient remains the original coefficient evaluated at d*n; no new
prime-factor independence is asserted. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem angular_stopped_divisor_character_sum (ℓ : ℤ) (X w z l b u : ℝ) (W : ι → ℝ → ℂ)
    (selected : Eisenstein → Eisenstein → Prop) (e v : Eisenstein)
    {d : Eisenstein} (hd : primary d) :
    (∑ n ∈ (stoppedIntervalSupport ι X l b e).filter (fun n => d ∣ n),
      angularStoppedRowCoefficient ℓ X w z u W selected n*cubicSymbol n v) =
      cubicSymbol d v*∑ n ∈ stoppedDivisorSlice ι X l b e d,
        angularStoppedRowCoefficient ℓ X w z u W selected (d*n)*cubicSymbol n v := by
  rw [stopped_divisor_sum_eq_slice X l b e hd,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  rw [cubicSymbol_mul_lower (primary_ne_zero hd)
    (primary_ne_zero (stoppedDivisorSlice_spec X l b e d hn).1)]
  ring


theorem angular_stopped_divisor_character_norm_le (ℓ : ℤ) (X w z l b u : ℝ) (W : ι → ℝ → ℂ)
    (selected : Eisenstein → Eisenstein → Prop) (e v : Eisenstein)
    {d : Eisenstein} (hd : primary d) :
    ‖∑ n ∈ (stoppedIntervalSupport ι X l b e).filter (fun n => d ∣ n),
      angularStoppedRowCoefficient ℓ X w z u W selected n*cubicSymbol n v‖ ≤
      ‖∑ n ∈ stoppedDivisorSlice ι X l b e d,
        angularStoppedRowCoefficient ℓ X w z u W selected (d*n)*cubicSymbol n v‖ := by
  rw [angular_stopped_divisor_character_sum ℓ X w z l b u W selected e v hd,norm_mul]
  exact mul_le_of_le_one_left (_root_.norm_nonneg _) (norm_cubicSymbol_le_one hd v)


theorem angular_stopped_slice_energy (ℓ : ℤ) (X w z l b u M : ℝ) (W : ι → ℝ → ℂ)
    (selected : Eisenstein → Eisenstein → Prop) (e d : Eisenstein)
    (hb : 0 ≤ b)
    (hcoeff : ∀ n ∈ stoppedIntervalSupport ι X l b e,
      ‖angularStoppedRowCoefficient ℓ X w z u W selected n‖ ≤ M) :
    (∑ n ∈ stoppedDivisorSlice ι X l b e d,
      ‖angularStoppedRowCoefficient ℓ X w z u W selected (d*n)‖^2) ≤
        18*(b/norm d)*M^2 := by
  have hc := primary_support_card_le (stoppedDivisorSlice ι X l b e d)
    (div_nonneg hb (norm_nonneg d))
    (fun n hn => ⟨(stoppedDivisorSlice_spec X l b e d hn).1,
      (stoppedDivisorSlice_spec X l b e d hn).2.2⟩)
  calc
    _ ≤ ∑ _n ∈ stoppedDivisorSlice ι X l b e d, M^2 := by
      apply Finset.sum_le_sum
      intro n hn
      exact pow_le_pow_left₀ (_root_.norm_nonneg _) (hcoeff _ (Finset.mem_filter.mp hn).2) 2
    _ = ((stoppedDivisorSlice ι X l b e d).card:ℝ)*M^2 := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right hc (sq_nonneg M)

end CubicFirstMoment

end

end OAI
