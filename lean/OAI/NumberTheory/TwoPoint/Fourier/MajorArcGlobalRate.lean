import OAI.NumberTheory.TwoPoint.Fourier.MajorArcPublishedRate

namespace OAI

/-! Absorb the initial dyadic block and quotient rounding after the
square-root character estimate, retaining the published energy rate. -/
namespace TwoPointCorrelations

lemma major_arc_boundary_rate {W q V H K : ℝ}
    (hW : 1 ≤ W) (hq : 1 ≤ q) (hqW : q ≤ W)
    (hK : (2*K+1)/V ≤ (W^4)⁻¹) (hH : W^3 ≤ H) :
    2*Real.sqrt q*(1+Real.log q)*q*((2*K+1)/V)+Real.sqrt q*q/H ≤ 3/W := by
  have hW0 : 0 < W := by linarith
  have hq0 : 0 < q := by linarith
  have hH0 : 0 < H := (pow_pos hW0 3).trans_le hH
  have hroot : Real.sqrt q ≤ W :=
    (Real.sqrt_le_self_iff.mpr (Or.inr hq)).trans hqW
  have hlog : 1+Real.log q ≤ W := by
    linarith [Real.log_le_sub_one_of_pos hq0]
  have hlog0 : 0 ≤ 1+Real.log q := by linarith [Real.log_nonneg hq]
  have hfirst : 2*Real.sqrt q*(1+Real.log q)*q*((2*K+1)/V) ≤ 2/W := by
    calc
      _ ≤ 2*Real.sqrt q*(1+Real.log q)*q*(W^4)⁻¹ :=
        mul_le_mul_of_nonneg_left hK (by positivity)
      _ ≤ 2*W*W*W*(W^4)⁻¹ := by gcongr
      _ = _ := by field_simp
  have hsecond : Real.sqrt q*q/H ≤ 1/W := by
    apply (div_le_iff₀ hH0).mpr
    calc
      _ ≤ W*W := mul_le_mul hroot hqW hq0.le hW0.le
      _ ≤ (1/W)*H := by
        rw [div_mul_eq_mul_div,one_mul]
        apply (le_div_iff₀ hW0).mpr
        simpa only [pow_succ,pow_two,pow_zero,one_mul] using hH
  calc
    _ ≤ 2/W+1/W := add_le_add hfirst hsecond
    _ = _ := by ring

lemma major_arc_global_normalized {I C R W q V H K : ℝ}
    (hC : 0 ≤ C) (hR : 0 ≤ R) (hW : 1 ≤ W) (hq : 1 ≤ q) (hqW : q ≤ W)
    (hV : 0 < V) (hK : (2*K+1)/V ≤ (W^4)⁻¹) (hH : W^3 ≤ H)
    (hi : I ≤ Real.sqrt q*((1+Real.log q)*
      (4*C*V*H*R+2*q*(2*K+1)*H)+q*V)) :
    I ≤ V*H*(4*C*(Real.sqrt W*(1+Real.log W))*R+3/W) := by
  have hW0 : 0 < W := by linarith
  have hH0 : 0 < H := (pow_pos hW0 3).trans_le hH
  have hq0 : 0 < q := by linarith
  have hweight : Real.sqrt q*(1+Real.log q) ≤ Real.sqrt W*(1+Real.log W) := by
    apply mul_le_mul (Real.sqrt_le_sqrt hqW)
      (by linarith [Real.log_le_log hq0 hqW])
      (by linarith [Real.log_nonneg hq]) (Real.sqrt_nonneg W)
  have hmain := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hweight (show 0 ≤ 4*C by positivity)) hR
  have herr := major_arc_boundary_rate hW hq hqW hK hH
  calc
    I ≤ Real.sqrt q*((1+Real.log q)*(4*C*V*H*R+2*q*(2*K+1)*H)+q*V) := hi
    _ = V*H*(4*C*(Real.sqrt q*(1+Real.log q))*R+
        (2*Real.sqrt q*(1+Real.log q)*q*((2*K+1)/V)+Real.sqrt q*q/H)) := by
      field_simp
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (add_le_add hmain herr) (mul_nonneg hV.le hH0.le)

end TwoPointCorrelations

end OAI
