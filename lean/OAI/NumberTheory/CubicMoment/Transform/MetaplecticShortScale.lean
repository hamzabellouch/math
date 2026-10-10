import OAI.NumberTheory.CubicMoment.Transform.MetaplecticPrimalShort

namespace OAI

/-! The short completed mean with an arbitrary fixed upper support
endpoint; the arithmetic length X is kept separate from that endpoint. -/
noncomputable section
open MeasureTheory
namespace CubicFirstMoment

lemma metaplectic_short_support_factor {B X R T : ℝ}
    (hB : 0 ≤ B) (hR : 1 ≤ R) (hT : 1 ≤ T)
    (hshort : X ≤ Real.sqrt R*T^2) :
    1+2*(B*X)/T ≤ (1+2*B)*Real.sqrt R*T := by
  have hTp : 0 < T := zero_lt_one.trans_le hT
  have hs : 1 ≤ Real.sqrt R := Real.one_le_sqrt.mpr hR
  have hRT : 1 ≤ Real.sqrt R*T := one_le_mul_of_one_le_of_one_le hs hT
  have hx : X/T ≤ Real.sqrt R*T := by
    apply (div_le_iff₀ hTp).mpr
    nlinarith only [hshort]
  have hb := mul_le_mul_of_nonneg_left hx (show 0 ≤ 2*B by positivity)
  calc
    _ = 1+(2*B)*(X/T) := by ring
    _ ≤ (1+2*B)*Real.sqrt R*T := by nlinarith only [hb,hRT]

/-- Actual finite primal coefficients supply this estimate, including
an arbitrary fixed support endpoint. -/
theorem metaplecticHeightCompleted_short_scaled_mean {ε C : ℝ} (hε : 0 < ε)
    (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C) :
    ∃ K : ℝ, 0 < K ∧ ∀ r : Eisenstein, primary r →
      ∀ (ℓ : ℤ) (W : ℝ → ℂ) (X B M T u R : ℝ),
      0 < X → 1 ≤ B → (∀ x : ℝ, B < x → W x = 0) →
      (∀ x : ℝ, ‖W x‖ ≤ M) → 1 ≤ B*X → 0 ≤ M → 1 ≤ T → 1 ≤ R →
      X ≤ Real.sqrt R*T^2 →
      (∫ t in T..2*T, ‖metaplecticHeightCompleted r ℓ W X (t+u)‖)/T ≤
        Real.sqrt (C*K*B^(1+ε)*(1+2*B)*X^(1+ε)*Real.sqrt R*T)*M := by
  obtain ⟨K,hK,hbound⟩ := metaplecticHeightCompleted_meanAbsolute_sq hε hMV hC
  refine ⟨K,hK,?_⟩
  intro r hr ℓ W X B M T u R hX hB hcut hW hVX hM hT hR hshort
  have hBp : 0 < B := zero_lt_one.trans_le hB
  have hsq := hbound r hr ℓ W X B (B*X) M T u hX le_rfl hcut hW hVX hM
    (zero_lt_one.trans_le hT)
  have hs := metaplectic_short_support_factor hBp.le hR hT hshort
  have hb : ((∫ t in T..2*T, ‖metaplecticHeightCompleted r ℓ W X (t+u)‖)/T)^2 ≤
      (C*K*B^(1+ε)*(1+2*B)*X^(1+ε)*Real.sqrt R*T)*M^2 := by
    apply hsq.trans
    calc
      _ = (C*K*(B*X)^(1+ε)*M^2)*(1+2*(B*X)/T) := by ring
      _ ≤ (C*K*(B*X)^(1+ε)*M^2)*((1+2*B)*Real.sqrt R*T) :=
        mul_le_mul_of_nonneg_left hs (by positivity)
      _ = _ := by rw [Real.mul_rpow hBp.le hX.le]; ring
  have hh := Real.le_sqrt_of_sq_le hb
  simpa only [Real.sqrt_mul (show 0 ≤ C*K*B^(1+ε)*(1+2*B)*X^(1+ε)*Real.sqrt R*T by positivity),
    Real.sqrt_sq hM] using hh

end CubicFirstMoment

end

end OAI
