import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Tactic

namespace OAI

/-! # A finite weighted pigeonhole principle for logarithmic prime blocks -/
namespace Ostmann
open scoped Classical BigOperators

theorem logarithmic_block_reciprocal_bound (F : Finset ℕ) (j : ℕ) (w c : ℝ)
    (hw : 0 < w) (hlog : ∀ p ∈ F, w * (j + 1) ≤ Real.log (p : ℝ))
    (hweight : (∑ p ∈ F, Real.log (p : ℝ) / p) ≤ c * w) :
    (∑ p ∈ F, (p : ℝ)⁻¹) ≤ c / (j + 1) := by
  have hh : w * ((j + 1 : ℝ) * ∑ p ∈ F, (p : ℝ)⁻¹) ≤ c * w := by
    calc
      _ = ∑ p ∈ F, (w * (j + 1)) * (p : ℝ)⁻¹ := by rw [← Finset.mul_sum]; ring
      _ ≤ ∑ p ∈ F, Real.log (p : ℝ) / p := by
        apply Finset.sum_le_sum
        intro p hp
        simpa only [div_eq_mul_inv] using
          mul_le_mul_of_nonneg_right (hlog p hp) (by positivity : 0 ≤ (p : ℝ)⁻¹)
      _ ≤ _ := hweight
  have hh' : (j + 1 : ℝ) * ∑ p ∈ F, (p : ℝ)⁻¹ ≤ c :=
    (mul_le_mul_iff_right₀ hw).mp (by nlinarith only [hh])
  apply (le_div_iff₀ (by positivity : (0 : ℝ) < j + 1)).mpr
  nlinarith only [hh']

theorem exists_logarithmic_heavy_fiber (F : Finset ℕ) (key : ℕ → ℕ) (N : ℕ)
    (w c : ℝ) (hw : 0 < w) (hc : 0 ≤ c)
    (hkey : ∀ p ∈ F, key p < N)
    (hlog : ∀ p ∈ F, w * (key p + 1) ≤ Real.log (p : ℝ))
    (hmass : c * (1 + Real.log N) < ∑ p ∈ F, (p : ℝ)⁻¹) :
    ∃ j ∈ Finset.range N, c * w <
      ∑ p ∈ F.filter (fun p => key p = j), Real.log (p : ℝ) / p := by
  by_contra hn
  push Not at hn
  have hbound (j : ℕ) (hj : j ∈ Finset.range N) :
      (∑ p ∈ F.filter (fun p => key p = j), (p : ℝ)⁻¹) ≤ c / (j + 1) := by
    apply logarithmic_block_reciprocal_bound _ j w c hw
    · intro p hp
      obtain ⟨hpF, hpj⟩ := Finset.mem_filter.mp hp
      simpa only [hpj] using hlog p hpF
    · exact hn j hj
  have hfib : (∑ j ∈ Finset.range N, ∑ p ∈ F.filter (fun p => key p = j), (p : ℝ)⁻¹) =
      ∑ p ∈ F, (p : ℝ)⁻¹ :=
    Finset.sum_fiberwise_of_maps_to (fun p hp => Finset.mem_range.mpr (hkey p hp)) _
  have hh : (∑ p ∈ F, (p : ℝ)⁻¹) ≤ c * (1 + Real.log N) := by
    calc
      _ = ∑ j ∈ Finset.range N, ∑ p ∈ F.filter (fun p => key p = j), (p : ℝ)⁻¹ := hfib.symm
      _ ≤ ∑ j ∈ Finset.range N, c / (j + 1) := Finset.sum_le_sum hbound
      _ = c * (harmonic N : ℝ) := by
        simp only [harmonic, Rat.cast_sum, Rat.cast_inv, Rat.cast_add, Rat.cast_natCast, Rat.cast_one, Nat.cast_add,
          Nat.cast_one, div_eq_mul_inv, Finset.mul_sum]
      _ ≤ _ := mul_le_mul_of_nonneg_left (harmonic_le_one_add_log N) hc
  linarith

theorem exists_logarithmic_heavy_interval (F : Finset ℕ) (a b w c : ℝ)
    (hw : 0 < w) (hw1 : 1 ≤ w) (ha : w ≤ a) (hc : 0 ≤ c)
    (hF : ∀ p ∈ F, a ≤ Real.log (p : ℝ) ∧ Real.log (p : ℝ) ≤ b)
    (hmass : c * (1 + Real.log (⌊b⌋₊ + 1 : ℕ)) < ∑ p ∈ F, (p : ℝ)⁻¹) :
    ∃ lo : ℝ, a ≤ lo ∧ lo ≤ b ∧
      c * w < ∑ p ∈ F.filter (fun p : ℕ => lo ≤ Real.log (p : ℝ) ∧ Real.log (p : ℝ) ≤ lo + w),
        Real.log (p : ℝ) / p := by
  let key := fun p : ℕ => ⌊(Real.log (p : ℝ) - a) / w⌋₊
  have hcell (p : ℕ) (hp : p ∈ F) :
      a + key p * w ≤ Real.log (p : ℝ) ∧ Real.log (p : ℝ) < a + key p * w + w := by
    have hnon : 0 ≤ (Real.log (p : ℝ) - a) / w := div_nonneg (by linarith [(hF p hp).1]) hw.le
    have hlow := (le_div_iff₀ hw).mp (Nat.floor_le hnon)
    have hhigh := (div_lt_iff₀ hw).mp (Nat.lt_floor_add_one ((Real.log (p : ℝ) - a) / w))
    dsimp [key]
    constructor <;> nlinarith
  have hkey (p : ℕ) (hp : p ∈ F) : key p < ⌊b⌋₊ + 1 := by
    have hk0 : (0 : ℝ) ≤ key p := Nat.cast_nonneg _
    have hlog0 : 0 ≤ Real.log (p : ℝ) := by linarith [(hF p hp).1]
    have hk : (key p : ℝ) ≤ Real.log (p : ℝ) := by
      have hh := mul_le_mul_of_nonneg_left hw1 hk0
      linarith [(hcell p hp).1]
    exact Nat.lt_succ_of_le (Nat.le_floor (hk.trans (hF p hp).2))
  obtain ⟨j, _, hj⟩ := exists_logarithmic_heavy_fiber F key (⌊b⌋₊ + 1) w c hw hc hkey
    (fun p hp => by nlinarith [(hcell p hp).1]) hmass
  have hne : (F.filter (fun p => key p = j)).Nonempty := by
    by_contra hn
    rw [Finset.not_nonempty_iff_eq_empty] at hn
    rw [hn, Finset.sum_empty] at hj
    exact (not_lt_of_ge (mul_nonneg hc hw.le)) hj
  obtain ⟨p, hp⟩ := hne
  obtain ⟨hpF, hpj⟩ := Finset.mem_filter.mp hp
  refine ⟨a + j * w, le_add_of_nonneg_right (by positivity), ?_, hj.trans_le ?_⟩
  · have hh := (hcell p hpF).1
    rw [hpj] at hh
    exact hh.trans (hF p hpF).2
  · apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro q hq
      obtain ⟨hqF, hqj⟩ := Finset.mem_filter.mp hq
      refine Finset.mem_filter.mpr ⟨hqF, ?_⟩
      have hh := hcell q hqF
      rw [hqj] at hh
      exact ⟨hh.1, hh.2.le⟩
    · intro q hq _
      exact div_nonneg (by linarith [(hF q (Finset.mem_filter.mp hq).1).1]) (Nat.cast_nonneg _)

end Ostmann

end OAI
