import OAI.NumberTheory.TwoPoint.Fourier.MinorArcPrimeKernel

namespace OAI

/-! The explicit minor-arc parameter saving for the four-prime kernel. -/

namespace TwoPointCorrelations

lemma minor_arc_parameter_bound (R H W q V : ℝ)
    (hR : 1 ≤ R) (hW : 1 ≤ W) (hWR : W ≤ R)
    (hWq : W ≤ q) (hqH : q ≤ H / W) (hRH : R ≤ H / W)
    (hV : 0 ≤ V) (hVR : V ≤ H / R) :
    2 * (3 * (4 * R + 1) / q + 1) * (2 * V + 4 * q * (1 + Real.log q)) ≤
      192 * H * (1 + Real.log H) / W := by
  have hR0 : 0 < R := by linarith
  have hW0 : 0 < W := by linarith
  have hq0 : 0 < q := lt_of_lt_of_le hW0 hWq
  have hH1 : 1 ≤ H := by
    have hwq : W * q ≤ H := by nlinarith [(le_div_iff₀ hW0).mp hqH]
    nlinarith
  have hH0 : 0 < H := by linarith
  have hqH' : q ≤ H := by
    have hmul := (le_div_iff₀ hW0).mp hqH
    nlinarith
  have hlogq : 0 ≤ Real.log q := Real.log_nonneg (hW.trans hWq)
  have hlogH : 0 ≤ Real.log H := Real.log_nonneg hH1
  have hlog : Real.log q ≤ Real.log H := Real.log_le_log hq0 hqH'
  have hA : 4 * R + 1 ≤ 5 * R := by linarith
  have h₁ : 12 * (4 * R + 1) * V / q ≤ 60 * H / W := by
    calc
      _ ≤ 12 * (5 * R) * (H / R) / q := by gcongr
      _ = 60 * H / q := by field_simp; ring
      _ ≤ _ := by gcongr
  have h₂ : 24 * (4 * R + 1) * (1 + Real.log q) ≤
      120 * (H / W) * (1 + Real.log H) := by
    calc
      _ ≤ 24 * (5 * R) * (1 + Real.log H) := by gcongr
      _ = 120 * R * (1 + Real.log H) := by ring
      _ ≤ _ := by gcongr
  have h₃ : 4 * V ≤ 4 * H / W := by
    calc
      _ ≤ 4 * (H / R) := mul_le_mul_of_nonneg_left hVR (by norm_num)
      _ = 4 * H / R := by ring
      _ ≤ _ := by gcongr
  have h₄ : 8 * q * (1 + Real.log q) ≤ 8 * (H / W) * (1 + Real.log H) := by
    gcongr
  have hsmall : 64 * H / W ≤ 64 * (H / W) * (1 + Real.log H) := by
    have hnonneg : 0 ≤ 64 * (H / W) := by positivity
    calc
      64 * H / W = (64 * (H / W)) * 1 := by ring
      _ ≤ (64 * (H / W)) * (1 + Real.log H) :=
        mul_le_mul_of_nonneg_left (by linarith) hnonneg
  have he : 2 * (3 * (4 * R + 1) / q + 1) * (2 * V + 4 * q * (1 + Real.log q)) =
      12 * (4 * R + 1) * V / q + 24 * (4 * R + 1) * (1 + Real.log q) +
        4 * V + 8 * q * (1 + Real.log q) := by field_simp; ring
  rw [he]
  calc
    _ ≤ (60 * H / W + 120 * (H / W) * (1 + Real.log H)) +
        4 * H / W + 8 * (H / W) * (1 + Real.log H) :=
      add_le_add (add_le_add (add_le_add h₁ h₂) h₃) h₄
    _ = 64 * H / W + 128 * (H / W) * (1 + Real.log H) := by ring
    _ ≤ 64 * (H / W) * (1 + Real.log H) +
        128 * (H / W) * (1 + Real.log H) := add_le_add hsmall le_rfl
    _ = 192 * H * (1 + Real.log H) / W := by ring

end TwoPointCorrelations

end OAI
