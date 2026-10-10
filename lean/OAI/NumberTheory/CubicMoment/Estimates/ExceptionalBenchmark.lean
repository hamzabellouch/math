import OAI.NumberTheory.CubicMoment.Estimates.NoncubePowerBounds

namespace OAI

/-! Normalize the exceptional moments by the actual local dispersion
benchmark B²(PQ²)^(1/3), retaining a positive power saving. -/
noncomputable section
namespace CubicFirstMoment

lemma exceptional_conductor_lower {p q ρ : ℝ} (hρ : 0 ≤ ρ)
    (hcase : (|p-1| ≤ ρ ∧ 0 ≤ q ∧ q ≤ ρ) ∨
      (|p-1/3| ≤ ρ ∧ |q-1/3| ≤ ρ)) : 1-3*ρ ≤ p+2*q := by
  rcases hcase with ⟨hp,hq,_⟩ | ⟨hp,hq⟩
  · linarith [(abs_le.mp hp).1]
  · linarith [(abs_le.mp hp).1,(abs_le.mp hq).1]

lemma conductor_rpow_identity {B : ℝ} (hB : 0 < B) (p q : ℝ) :
    (B^p*(B^q)^2)^(1/3:ℝ) = B^((p+2*q)/3) := by
  rw [← Real.rpow_natCast (B^q) 2,← Real.rpow_mul hB.le]
  norm_num only [Nat.cast_ofNat]
  rw [← Real.rpow_add hB,← Real.rpow_mul hB.le]
  congr 1
  ring

theorem exceptional_moment_benchmark {B p q ρ ε E : ℝ}
    (hB : 1 ≤ B) (hρ : 0 ≤ ρ) (hρε : ρ ≤ ε/2)
    (hcase : (|p-1| ≤ ρ ∧ 0 ≤ q ∧ q ≤ ρ) ∨
      (|p-1/3| ≤ ρ ∧ |q-1/3| ≤ ρ))
    (hE : E ≤ B^(7/3-ε)) :
    E ≤ B^2*(B^p*(B^q)^2)^(1/3:ℝ)*B^(-ε/2) := by
  have hBp : 0 < B := zero_lt_one.trans_le hB
  have hlo := exceptional_conductor_lower hρ hcase
  apply hE.trans
  rw [conductor_rpow_identity hBp,← Real.rpow_two,← Real.rpow_add hBp,← Real.rpow_add hBp]
  exact Real.rpow_le_rpow_of_exponent_le hB (by linarith)

end CubicFirstMoment

end

end OAI
