import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralThreeRegionBounds

namespace OAI

/-! Propagate an endpoint state and an outgoing state with separate constants,
retaining the action only on the forbidden part of the interval. -/

open Set
namespace DefocusingNLS

theorem spectralThreeRegion_forward (R a b E A C D : ℝ)
    (hRa : R ≤ a) (hab : a ≤ b) (hbE : b ≤ E)
    (hA : 0 ≤ A) (hC : 0 ≤ C) (hD : 1 ≤ D)
    (N H : ℝ → ℝ) (hNR : 0 ≤ N R) (ha : H a = 0)
    (hleft : ∀ r ∈ Icc R a, N r ≤ A*Real.exp (H R-H r)*N R)
    (hcentral : ∀ r ∈ Icc a b, N r ≤ C*N a)
    (hright : ∀ r ∈ Icc b E, N r ≤ D*N b) :
    ∀ r ∈ Icc R E, N r ≤ max A (C*A*D)*
      Real.exp (H R-spectralTruncatedAction a H r)*N R := by
  have haN : N a ≤ A*(Real.exp (H R)*N R) := by
    simpa only [ha,sub_zero,mul_assoc] using hleft a ⟨hRa,le_rfl⟩
  have hcN (r : ℝ) (hr : r ∈ Icc a b) : N r ≤ (C*A)*(Real.exp (H R)*N R) := by
    calc
      N r ≤ C*N a := hcentral r hr
      _ ≤ C*(A*(Real.exp (H R)*N R)) := mul_le_mul_of_nonneg_left haN hC
      _ = _ := by ring
  have hh := spectralThreeRegion_bound R a b E A (C*A) D (Real.exp (H R)*N R)
    hRa hab hbE hA (mul_nonneg hC hA) hD (mul_nonneg (Real.exp_pos _).le hNR)
    N (fun r => -H r) (by simp only [ha,neg_zero])
    (fun r hr => by
      convert hleft r hr using 1
      rw [Real.exp_sub,Real.exp_neg]
      field_simp
      ) hcN hright
  intro r hr
  have he : spectralTruncatedAction a (fun s => -H s) r = -spectralTruncatedAction a H r := by
    unfold spectralTruncatedAction
    split_ifs <;> simp only [neg_zero]
  have hb := hh r hr
  rw [he] at hb
  convert hb using 1
  rw [Real.exp_sub,Real.exp_neg]
  field_simp

end DefocusingNLS

end OAI
