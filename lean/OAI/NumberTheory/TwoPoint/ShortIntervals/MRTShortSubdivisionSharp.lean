import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTArcSubdivision

namespace OAI

/-! Subdivision with the exact common outer cutoff.  The last complete
block starts no later than H-h, so its short window stays below X+H. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

lemma mrt_subdivision_shift_le {H h j : ℕ} (hj : j ∈ range (H/h)) :
    j*h ≤ H-h := by
  have hs : (j+1)*h ≤ H :=
    (Nat.mul_le_mul_right h (Nat.succ_le_of_lt (mem_range.mp hj))).trans
      (Nat.div_mul_le_self H h)
  rw [Nat.add_mul,one_mul] at hs
  omega

theorem mrt_short_integral_subdivision_sharp (F : ℕ → ℂ) (hF : OneBounded F)
    (X H h : ℕ) (hh : 0 < h) (hhH : h ≤ H) (α : ℝ) :
    shortExponentialIntegral F X H α ≤
      (H/h:ℕ)*shortExponentialIntegral F (X+H-h) h α+(X:ℝ)*h := by
  have hshift (j : ℕ) (hj : j ∈ range (H/h)) :
      (∑ v ∈ range X, ‖shortExponentialSum F h α (v+j*h:ℕ)‖) ≤
        ∑ v ∈ range (X+H-h), ‖shortExponentialSum F h α v‖ := by
    have hle := mrt_subdivision_shift_le hj
    have hinj : Set.InjOn (fun v : ℕ => v+j*h) (range X) := by
      intro v _ w _ hvw
      exact Nat.add_right_cancel hvw
    calc
      _ = ∑ v ∈ (range X).image (fun v => v+j*h), ‖shortExponentialSum F h α v‖ := by
        rw [sum_image hinj]
      _ ≤ _ := by
        apply sum_le_sum_of_subset_of_nonneg
        · intro v hv
          obtain ⟨w,hw,rfl⟩ := mem_image.mp hv
          exact mem_range.mpr (by have hw' := mem_range.mp hw; omega)
        · intro v _ _
          exact norm_nonneg _
  simp only [shortExponentialIntegral_eq_sum]
  calc
    _ ≤ ∑ v ∈ range X,
        ((∑ j ∈ range (H/h), ‖shortExponentialSum F h α (v+j*h:ℕ)‖)+(h:ℝ)) :=
      sum_le_sum (fun v _ => mrt_short_subdivision_pointwise F hF H h v hh α)
    _ = (∑ j ∈ range (H/h), ∑ v ∈ range X,
        ‖shortExponentialSum F h α (v+j*h:ℕ)‖)+(X:ℝ)*h := by
      rw [sum_add_distrib,sum_comm]
      simp
    _ ≤ (∑ _j ∈ range (H/h), ∑ v ∈ range (X+H-h),
        ‖shortExponentialSum F h α v‖)+(X:ℝ)*h :=
      add_le_add (sum_le_sum hshift) le_rfl
    _ = _ := by simp

theorem mrt_arc_subdivision_integral_sharp (F : ℕ → ℂ) (hF : OneBounded F)
    (X H : ℕ) (hHX : H ≤ X) {W ε : ℝ}
    (hW : 2 ≤ W) (hH : W^(250:ℕ) ≤ (H:ℝ)) (hε : 0 ≤ ε) (α : ℝ)
    (hshort : shortExponentialIntegral F (X+H-mrtArcSubdivisionLength H W)
      (mrtArcSubdivisionLength H W) α ≤
      ε*(X+H-mrtArcSubdivisionLength H W:ℕ)*(mrtArcSubdivisionLength H W:ℝ)) :
    shortExponentialIntegral F X H α ≤
      (X:ℝ)*H*(2*ε+W^(-(1/4:ℝ))) := by
  let h := mrtArcSubdivisionLength H W
  have hh : 0 < h := (mrt_arc_subdivision_bounds hW hH).1
  have hhH : h ≤ H := (mrt_arc_subdivision_bounds hW hH).2.1
  have hH0 : (0:ℝ)<H := (pow_pos (by linarith : 0<W) 250).trans_le hH
  have hcount : (H/h:ℕ)*(h:ℝ) ≤ H := by
    exact_mod_cast Nat.div_mul_le_self H h
  have hX : (X+H-h:ℕ) ≤ (2:ℝ)*X := by
    exact_mod_cast (by omega : X+H-h ≤ 2*X)
  have hmain : (H/h:ℕ)*shortExponentialIntegral F (X+H-h) h α ≤
      2*ε*X*H := by
    calc
      _ ≤ (H/h:ℕ)*(ε*(X+H-h:ℕ)*(h:ℝ)) :=
        mul_le_mul_of_nonneg_left hshort (Nat.cast_nonneg _)
      _ = (ε*(X+H-h:ℕ))*((H/h:ℕ)*(h:ℝ)) := by ring
      _ ≤ (ε*((2:ℝ)*X))*(H:ℝ) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hX hε) hcount
          (by positivity) (by positivity)
      _ = _ := by ring
  have hrem : (X:ℝ)*h ≤ (X:ℝ)*H*W^(-(1/4:ℝ)) := by
    have hb := (div_le_iff₀ hH0).mp (mrt_arc_subdivision_remainder hW hH)
    simpa only [mul_assoc,mul_comm,mul_left_comm] using
      mul_le_mul_of_nonneg_left hb (Nat.cast_nonneg X)
  calc
    _ ≤ (H/h:ℕ)*shortExponentialIntegral F (X+H-h) h α+(X:ℝ)*h :=
      mrt_short_integral_subdivision_sharp F hF X H h hh hhH α
    _ ≤ 2*ε*X*H+(X:ℝ)*H*W^(-(1/4:ℝ)) := add_le_add hmain hrem
    _ = _ := by ring

end TwoPointCorrelations

end OAI
