import Mathlib.Data.Nat.GCD.Basic
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic.FrequencyLCM
open scoped BigOperators

def gcdCoordinates (z : ℕ × ℕ) : ℕ × ℕ × ℕ :=
  (z.1.gcd z.2, z.1 / z.1.gcd z.2, z.2 / z.1.gcd z.2)

theorem gcdCoordinates_injective : Function.Injective gcdCoordinates := by
  intro x y h
  have hd : x.1.gcd x.2 = y.1.gcd y.2 := congrArg Prod.fst h
  have hu : x.1 / x.1.gcd x.2 = y.1 / y.1.gcd y.2 := congrArg (fun t => t.2.1) h
  have hv : x.2 / x.1.gcd x.2 = y.2 / y.1.gcd y.2 := congrArg (fun t => t.2.2) h
  apply Prod.ext
  · calc
      x.1 = x.1.gcd x.2 * (x.1 / x.1.gcd x.2) := (Nat.mul_div_cancel' (Nat.gcd_dvd_left _ _)).symm
      _ = y.1.gcd y.2 * (y.1 / y.1.gcd y.2) := by rw [hu,hd]
      _ = y.1 := Nat.mul_div_cancel' (Nat.gcd_dvd_left _ _)
  · calc
      x.2 = x.1.gcd x.2 * (x.2 / x.1.gcd x.2) := (Nat.mul_div_cancel' (Nat.gcd_dvd_right _ _)).symm
      _ = y.1.gcd y.2 * (y.2 / y.1.gcd y.2) := by rw [hv,hd]
      _ = y.2 := Nat.mul_div_cancel' (Nat.gcd_dvd_right _ _)

theorem lcm_gcdCoordinates {a b : ℕ} (ha : 0 < a) :
    a.lcm b = a.gcd b * (a/a.gcd b) * (b/a.gcd b) := by
  have hg : 0 < a.gcd b := Nat.gcd_pos_of_pos_left b ha
  apply Nat.eq_of_mul_eq_mul_left hg
  have h₁ := Nat.mul_div_cancel' (Nat.gcd_dvd_left a b)
  have h₂ := Nat.mul_div_cancel' (Nat.gcd_dvd_right a b)
  have h₃ := Nat.gcd_mul_lcm a b
  nlinarith

theorem reciprocal_lcm_sum_le (V : ℕ) :
    (∑ a ∈ Finset.Icc 1 V, ∑ b ∈ Finset.Icc 1 V, ((a.lcm b : ℕ):ℝ)⁻¹) ≤
      (∑ a ∈ Finset.Icc 1 V, (a:ℝ)⁻¹)^3 := by
  let S := Finset.Icc 1 V
  let T := S ×ˢ (S ×ˢ S)
  let w : ℕ × ℕ × ℕ → ℝ := fun t => (t.1:ℝ)⁻¹*(t.2.1:ℝ)⁻¹*(t.2.2:ℝ)⁻¹
  have hsub : (S ×ˢ S).image gcdCoordinates ⊆ T := by
    intro t ht
    obtain ⟨⟨a,b⟩,hab,rfl⟩ := Finset.mem_image.mp ht
    obtain ⟨ha,hb⟩ := Finset.mem_product.mp hab
    obtain ⟨ha1,haV⟩ := Finset.mem_Icc.mp ha
    obtain ⟨hb1,hbV⟩ := Finset.mem_Icc.mp hb
    have hg : 0 < a.gcd b := Nat.gcd_pos_of_pos_left b ha1
    have hga : a.gcd b ≤ a := Nat.gcd_le_left b ha1
    have hgb : a.gcd b ≤ b := Nat.gcd_le_right a hb1
    have hua : 1 ≤ a / a.gcd b := Nat.one_le_div_iff hg |>.2 hga
    have hub : 1 ≤ b / a.gcd b := Nat.one_le_div_iff hg |>.2 hgb
    exact Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr ⟨hg,hga.trans haV⟩,
      Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr ⟨hua,(Nat.div_le_self _ _).trans haV⟩,
        Finset.mem_Icc.mpr ⟨hub,(Nat.div_le_self _ _).trans hbV⟩⟩⟩
  calc
    _ = ∑ z ∈ S ×ˢ S, w (gcdCoordinates z) := by
      rw [Finset.sum_product]
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro b hb
      rw [lcm_gcdCoordinates (Finset.mem_Icc.mp ha).1]
      simp [w,gcdCoordinates,mul_inv_rev, mul_comm, mul_left_comm, mul_assoc]
    _ = ∑ t ∈ (S ×ˢ S).image gcdCoordinates, w t :=
      (Finset.sum_image (fun _ _ _ _ h => gcdCoordinates_injective h)).symm
    _ ≤ ∑ t ∈ T, w t := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by
      dsimp [w]; positivity)
    _ = _ := by
      simp only [T,w,Finset.sum_product, ← Finset.mul_sum, ← Finset.sum_mul]
      ring

theorem reciprocal_lcm_sum_le_log (V : ℕ) :
    (∑ a ∈ Finset.Icc 1 V, ∑ b ∈ Finset.Icc 1 V, ((a.lcm b : ℕ):ℝ)⁻¹) ≤
      (1+Real.log V)^3 := by
  apply (reciprocal_lcm_sum_le V).trans
  have h := harmonic_le_one_add_log V
  simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast] at h
  exact pow_le_pow_left₀ (by positivity) h 3

end Ostmann.Arithmetic.FrequencyLCM

end

end OAI
