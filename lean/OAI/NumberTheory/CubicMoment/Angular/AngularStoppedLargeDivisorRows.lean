import OAI.NumberTheory.CubicMoment.Angular.AngularStoppedCharacterRows
import OAI.NumberTheory.CubicMoment.Angular.AngularStoppedFilteredCore
import OAI.NumberTheory.CubicMoment.Angular.AngularStoppedMellinRows
import OAI.NumberTheory.CubicMoment.Decomposition.StoppedLargeDivisorRows
import OAI.NumberTheory.CubicMoment.Decomposition.StoppedDivisorScale

namespace OAI

/-! Normalize a single large-divisor row before summing the divisor norms. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem angular_stopped_large_divisor_row (ℓ : ℤ) {ε : ℝ} (hε : 0 < ε) :
    ∃ K : ℝ, 0 < K ∧ ∀ (X w z l b u M B : ℝ)
      (W : ι → ℝ → ℂ) (selected : Eisenstein → Eisenstein → Prop)
      (e d : Eisenstein), primary d → 0 < b → 1 ≤ B → norm d ≤ b →
      (∀ n ∈ stoppedIntervalSupport ι X l b e,
        ‖angularStoppedRowCoefficient ℓ X w z u W selected n‖ ≤ M) →
      ∀ H : Finset Eisenstein, (∀ v ∈ H, v ≠ 0 ∧ norm v ≤ B) →
      (∑ v ∈ H, ‖∑ n ∈ (stoppedIntervalSupport ι X l b e).filter
        (fun n => d ∣ n),
        angularStoppedRowCoefficient ℓ X w z u W selected n*cubicSymbol n v‖^2) ≤
      (K*(2*B*b)^ε*M^2)*(B*b*norm d^(-1:ℝ)+
        B^(2/3:ℝ)*b^(5/3:ℝ)*norm d^(-5/3:ℝ)+
        B^(1/3:ℝ)*b^2*norm d^(-2:ℝ)) := by
  obtain ⟨K,hK,hbound⟩ := angular_stopped_filtered_outer_sieve ℓ (ι := ι) hε
  refine ⟨K,hK,?_⟩
  intro X w z l b u M B W selected e d hd hb hB hdb hcoeff H hH
  have hq := norm_pos_of_ne_zero (primary_ne_zero hd)
  have hqone := one_le_norm (primary_ne_zero hd)
  have hraw := hbound X w z l b u M B W selected e d
    hd hb.le hB ((le_div_iff₀ hq).mpr (by simpa using hdb)) hcoeff H hH
  have hh := stopped_outer_row_scale_le hb hqone (zero_le_one.trans hB) hε.le
  calc
    _ ≤ K*((2*B*(b/norm d))^ε*
        (B+(B*(b/norm d))^(2/3:ℝ)+B^(1/3:ℝ)*(b/norm d))*
        (b/norm d))*M^2 := hraw.trans_eq (by ring)
    _ ≤ K*((2*B*b)^ε*(B*b*norm d^(-1:ℝ)+
        B^(2/3:ℝ)*b^(5/3:ℝ)*norm d^(-5/3:ℝ)+
        B^(1/3:ℝ)*b^2*norm d^(-2:ℝ)))*M^2 :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hh hK.le) (sq_nonneg M)
    _ = _ := by ring

end CubicFirstMoment

end

end OAI
