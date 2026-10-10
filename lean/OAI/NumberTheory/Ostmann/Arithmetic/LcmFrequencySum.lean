import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

namespace OAI

/-! # The reciprocal-lcm sum in the frequency budget

The gcd coordinates embed each frequency pair into three independent
positive harmonic sums. No asymptotic divisor estimate is used here.
-/

namespace Ostmann

open scoped BigOperators

def gcdFrequencyCoordinates (x : ℕ × ℕ) : ℕ × ℕ × ℕ :=
  (x.1.gcd x.2, x.1 / x.1.gcd x.2, x.2 / x.1.gcd x.2)

theorem gcdFrequencyCoordinates_recover (x : ℕ × ℕ) :
    (gcdFrequencyCoordinates x).1 * (gcdFrequencyCoordinates x).2.1 = x.1 ∧
    (gcdFrequencyCoordinates x).1 * (gcdFrequencyCoordinates x).2.2 = x.2 := by
  exact ⟨Nat.mul_div_cancel' (Nat.gcd_dvd_left _ _),
    Nat.mul_div_cancel' (Nat.gcd_dvd_right _ _)⟩

theorem gcdFrequencyCoordinates_injective : Function.Injective gcdFrequencyCoordinates := by
  intro x y h
  obtain ⟨hx₁, hx₂⟩ := gcdFrequencyCoordinates_recover x
  obtain ⟨hy₁, hy₂⟩ := gcdFrequencyCoordinates_recover y
  apply Prod.ext
  · exact hx₁.symm.trans ((congrArg (fun z : ℕ × ℕ × ℕ => z.1 * z.2.1) h).trans hy₁)
  · exact hx₂.symm.trans ((congrArg (fun z : ℕ × ℕ × ℕ => z.1 * z.2.2) h).trans hy₂)

theorem gcdFrequencyCoordinates_lcm (a b : ℕ) (ha : 0 < a) :
    (gcdFrequencyCoordinates (a, b)).1 * (gcdFrequencyCoordinates (a, b)).2.1 *
      (gcdFrequencyCoordinates (a, b)).2.2 = a.lcm b := by
  have hg := Nat.gcd_pos_of_pos_left b ha
  obtain ⟨ha', hb'⟩ := gcdFrequencyCoordinates_recover (a, b)
  apply Nat.eq_of_mul_eq_mul_left hg
  calc
    _ = ((gcdFrequencyCoordinates (a, b)).1 * (gcdFrequencyCoordinates (a, b)).2.1) *
        ((gcdFrequencyCoordinates (a, b)).1 * (gcdFrequencyCoordinates (a, b)).2.2) := by
      dsimp [gcdFrequencyCoordinates]
      ring
    _ = a * b := by rw [ha', hb']
    _ = _ := (Nat.gcd_mul_lcm a b).symm

theorem gcdFrequencyCoordinates_mem {N a b : ℕ}
    (ha : a ∈ Finset.Icc 1 N) (hb : b ∈ Finset.Icc 1 N) :
    gcdFrequencyCoordinates (a, b) ∈
      (Finset.Icc 1 N).product ((Finset.Icc 1 N).product (Finset.Icc 1 N)) := by
  obtain ⟨ha₀, haN⟩ := Finset.mem_Icc.mp ha
  obtain ⟨hb₀, hbN⟩ := Finset.mem_Icc.mp hb
  have hap : 0 < a := ha₀
  have hbp : 0 < b := hb₀
  have hg := Nat.gcd_pos_of_pos_left b hap
  have hga := Nat.le_of_dvd hap (Nat.gcd_dvd_left a b)
  have hgb := Nat.le_of_dvd hbp (Nat.gcd_dvd_right a b)
  apply Finset.mem_product.mpr
  refine ⟨Finset.mem_Icc.mpr ⟨hg, hga.trans haN⟩, Finset.mem_product.mpr ⟨?_, ?_⟩⟩
  · exact Finset.mem_Icc.mpr ⟨Nat.div_pos hga hg, (Nat.div_le_self _ _).trans haN⟩
  · exact Finset.mem_Icc.mpr ⟨Nat.div_pos hgb hg, (Nat.div_le_self _ _).trans hbN⟩

/-- Exact finite bound before estimating the harmonic sum. -/
theorem reciprocal_lcm_sum_le_harmonic_cube (N : ℕ) :
    (∑ a ∈ Finset.Icc 1 N, ∑ b ∈ Finset.Icc 1 N, ((a.lcm b : ℕ) : ℝ)⁻¹) ≤
      (∑ n ∈ Finset.Icc 1 N, (n : ℝ)⁻¹) ^ 3 := by
  let S := Finset.Icc 1 N
  let w : ℕ × ℕ × ℕ → ℝ := fun z => (z.1 : ℝ)⁻¹ * (z.2.1 : ℝ)⁻¹ * (z.2.2 : ℝ)⁻¹
  have hw (x : ℕ × ℕ) (hx : x ∈ S.product S) :
      ((x.1.lcm x.2 : ℕ) : ℝ)⁻¹ = w (gcdFrequencyCoordinates x) := by
    have ha : 0 < x.1 := (Finset.mem_Icc.mp (Finset.mem_product.mp hx).1).1
    rw [← gcdFrequencyCoordinates_lcm x.1 x.2 ha]
    simp only [w, Nat.cast_mul, mul_inv_rev]
    ring
  have hsub : (S.product S).image gcdFrequencyCoordinates ⊆ S.product (S.product S) := by
    intro z hz
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hz
    exact gcdFrequencyCoordinates_mem (Finset.mem_product.mp hx).1 (Finset.mem_product.mp hx).2
  calc
    _ = ∑ x ∈ S.product S, w (gcdFrequencyCoordinates x) := by
      simp only [Finset.product_eq_sprod]
      rw [Finset.sum_product S S (fun x => w (gcdFrequencyCoordinates x))]
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro b hb
      exact hw (a, b) (Finset.mem_product.mpr ⟨ha, hb⟩)
    _ = ∑ z ∈ (S.product S).image gcdFrequencyCoordinates, w z := by
      exact (Finset.sum_image (fun _ _ _ _ h => gcdFrequencyCoordinates_injective h)).symm
    _ ≤ ∑ z ∈ S.product (S.product S), w z :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by dsimp [w]; positivity)
    _ = ∑ a ∈ S, ∑ b ∈ S, ∑ c ∈ S, (a : ℝ)⁻¹ * (b : ℝ)⁻¹ * (c : ℝ)⁻¹ := by
      simp only [Finset.product_eq_sprod]
      rw [Finset.sum_product S (S ×ˢ S) w]
      apply Finset.sum_congr rfl
      intro a _
      exact Finset.sum_product S S (fun z => w (a, z))
    _ = _ := by
      simp only [← Finset.mul_sum, ← Finset.sum_mul]
      dsimp [S]
      ring

/-- The quantitative frequency-pair estimate used by the norm comparison. -/
theorem reciprocal_lcm_sum_le_log_cube (N : ℕ) :
    (∑ a ∈ Finset.Icc 1 N, ∑ b ∈ Finset.Icc 1 N, ((a.lcm b : ℕ) : ℝ)⁻¹) ≤
      (1 + Real.log N) ^ 3 := by
  have hH : (∑ n ∈ Finset.Icc 1 N, (n : ℝ)⁻¹) ≤ 1 + Real.log N := by
    simpa only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
      using harmonic_le_one_add_log N
  exact (reciprocal_lcm_sum_le_harmonic_cube N).trans
    (pow_le_pow_left₀ (Finset.sum_nonneg fun _ _ => by positivity) hH 3)

end Ostmann

end OAI
