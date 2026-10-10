import OAI.NumberTheory.CubicMoment.Transform.MetaplecticPrimalFinite

namespace OAI

/-! The short-polynomial branch of the completed angular height bound. -/
noncomputable section
open MeasureTheory
namespace CubicFirstMoment

lemma metaplectic_short_height_factor {V R T : ℝ}
    (hR : 1 ≤ R) (hT : 1 ≤ T) (hV : V ≤ Real.sqrt R*T^2) :
    1+2*V/T ≤ 3*Real.sqrt R*T := by
  have hTp : 0 < T := zero_lt_one.trans_le hT
  have hs : 1 ≤ Real.sqrt R := Real.one_le_sqrt.mpr hR
  have hVT : V/T ≤ Real.sqrt R*T := by
    apply (div_le_iff₀ hTp).mpr
    nlinarith
  have hRT : 1 ≤ Real.sqrt R*T := by
    simpa only [one_mul] using mul_le_mul hs hT zero_le_one (Real.sqrt_nonneg R)
  calc
    1+2*V/T = 1+2*(V/T) := by ring
    _ ≤ 3*Real.sqrt R*T := by linarith

/-- For V≤sqrt(R)T² the literal completed angular sum has mean size
O(V^(1/2+epsilon) R^(1/4) sqrt(T)); the displayed square root keeps the
exact coefficient constants and avoids hidden normalization factors. -/
theorem metaplecticHeightCompleted_short_mean {ε C : ℝ} (hε : 0 < ε)
    (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C) :
    ∃ K : ℝ, 0 < K ∧ ∀ r : Eisenstein, primary r →
      ∀ (ℓ : ℤ) (W : ℝ → ℂ) (X B V M T u R : ℝ),
      0 < X → B*X ≤ V → (∀ x : ℝ, B < x → W x = 0) →
      (∀ x : ℝ, ‖W x‖ ≤ M) → 1 ≤ V → 0 ≤ M → 1 ≤ T → 1 ≤ R →
      V ≤ Real.sqrt R*T^2 →
      (∫ t in T..2*T, ‖metaplecticHeightCompleted r ℓ W X (t+u)‖)/T ≤
        Real.sqrt (3*C*K*V^(1+ε)*Real.sqrt R*T)*M := by
  obtain ⟨K,hK,hbound⟩ := metaplecticHeightCompleted_meanAbsolute_sq hε hMV hC
  refine ⟨K,hK,?_⟩
  intro r hr ℓ W X B V M T u R hX hBX hcut hW hV hM hT hR hlength
  have hsq := hbound r hr ℓ W X B V M T u hX hBX hcut hW hV hM (zero_lt_one.trans_le hT)
  have hf := metaplectic_short_height_factor hR hT hlength
  have hb : ((∫ t in T..2*T, ‖metaplecticHeightCompleted r ℓ W X (t+u)‖)/T)^2 ≤
      (3*C*K*V^(1+ε)*Real.sqrt R*T)*M^2 := by
    apply hsq.trans
    calc
      _ = (C*K*V^(1+ε)*M^2)*(1+2*V/T) := by ring
      _ ≤ (C*K*V^(1+ε)*M^2)*(3*Real.sqrt R*T) :=
        mul_le_mul_of_nonneg_left hf (by positivity)
      _ = _ := by ring
  have hh := Real.le_sqrt_of_sq_le hb
  simpa only [Real.sqrt_mul (show 0 ≤ 3*C*K*V^(1+ε)*Real.sqrt R*T by positivity),
    Real.sqrt_sq hM] using hh

end CubicFirstMoment

end

end OAI
