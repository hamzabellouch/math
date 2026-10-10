import OAI.NumberTheory.TwoPoint.Fourier.MinorArcTrivial

namespace OAI

/-! Subdivision into fixed short lengths, retaining the additive
frequency and allowing all shifted origins in one enlarged prefix. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

lemma mrt_short_sum_append (F : ℕ → ℂ) (a b v : ℕ) (α : ℝ) :
    shortExponentialSum F (a+b) α v =
      shortExponentialSum F a α v + shortExponentialSum F b α (v+a:ℕ) := by
  simp only [shortExponentialSum_at_nat, sum_Icc_shift]
  rw [sum_range_add]
  congr 1
  apply sum_congr rfl
  intro n _
  simp only [Nat.add_assoc]

lemma mrt_short_sum_blocks (F : ℕ → ℂ) (h K v : ℕ) (α : ℝ) :
    shortExponentialSum F (K*h) α v =
      ∑ j ∈ range K, shortExponentialSum F h α (v+j*h:ℕ) := by
  induction K with
  | zero =>
    simp only [zero_mul, shortExponentialSum_at_nat, sum_Icc_shift, sum_range_zero]
  | succ K ih =>
    rw [show (K+1)*h = K*h+h by ring, mrt_short_sum_append, ih, sum_range_succ]

lemma mrt_short_subdivision_pointwise (F : ℕ → ℂ) (hF : OneBounded F)
    (H h v : ℕ) (hh : 0 < h) (α : ℝ) :
    ‖shortExponentialSum F H α v‖ ≤
      (∑ j ∈ range (H/h), ‖shortExponentialSum F h α (v+j*h:ℕ)‖)+(h:ℝ) := by
  have he : H = (H/h)*h+H%h := by
    simpa only [Nat.mul_comm] using (Nat.div_add_mod H h).symm
  have hs := mrt_short_sum_append F ((H/h)*h) (H%h) v α
  rw [← he] at hs
  have hsum : ‖∑ j ∈ range (H/h), shortExponentialSum F h α (v+j*h:ℕ)‖ ≤
      ∑ j ∈ range (H/h), ‖shortExponentialSum F h α (v+j*h:ℕ)‖ :=
    norm_sum_le _ _
  have hrest₀ : ‖shortExponentialSum F (H%h) α (v+(H/h)*h:ℕ)‖ ≤ (H%h:ℕ) :=
    minor_arc_short_sum_trivial F hF (H%h) (v+(H/h)*h) α
  have hrest : ‖shortExponentialSum F (H%h) α (v+(H/h)*h:ℕ)‖ ≤ (h:ℝ) :=
    hrest₀.trans (by exact_mod_cast (Nat.mod_lt H hh).le)
  rw [hs, mrt_short_sum_blocks]
  exact (norm_add_le _ _).trans (add_le_add hsum hrest)

theorem mrt_short_integral_subdivision (F : ℕ → ℂ) (hF : OneBounded F)
    (X H h : ℕ) (hh : 0 < h) (α : ℝ) :
    shortExponentialIntegral F X H α ≤
      (H/h:ℕ)*shortExponentialIntegral F (X+H) h α+(X:ℝ)*h := by
  have hshift (j : ℕ) (hj : j ∈ range (H/h)) :
      (∑ v ∈ range X, ‖shortExponentialSum F h α (v+j*h:ℕ)‖) ≤
        ∑ v ∈ range (X+H), ‖shortExponentialSum F h α v‖ := by
    have hle : j*h ≤ H :=
      (Nat.mul_le_mul_right h (Nat.le_of_lt (mem_range.mp hj))).trans (Nat.div_mul_le_self H h)
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
      rw [sum_add_distrib, sum_comm]
      simp
    _ ≤ (∑ _j ∈ range (H/h), ∑ v ∈ range (X+H),
        ‖shortExponentialSum F h α v‖)+(X:ℝ)*h :=
      add_le_add (sum_le_sum hshift) le_rfl
    _ = _ := by simp

end TwoPointCorrelations

end OAI
