import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Data.Rat.Floor
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace OAI

open scoped BigOperators

namespace Ostmann.ZeroDensity

theorem extend_density_bound {ι : Type*} (s : Finset ι) (gap : ι → ℝ)
    {A B u b : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hub : u ≤ b)
    (htop : ∀ i ∈ s, gap i ≤ b)
    (hdensity : ∀ t ∈ Set.Icc u b,
      ((s.filter (fun i => gap i ≤ t)).card : ℝ) ≤ B * Real.exp (A * t)) :
    ∀ t, u ≤ t →
      ((s.filter (fun i => gap i ≤ t)).card : ℝ) ≤ B * Real.exp (A * t) := by
  classical
  intro t hut
  by_cases htb : t ≤ b
  · exact hdensity t ⟨hut, htb⟩
  · have hbt : b ≤ t := le_of_not_ge htb
    have hb := hdensity b ⟨hub, le_rfl⟩
    have hfilter : s.filter (fun i => gap i ≤ b) = s := by
      exact Finset.filter_true_of_mem htop
    rw [hfilter] at hb
    calc
      ((s.filter (fun i => gap i ≤ t)).card : ℝ) ≤ (s.card : ℝ) := by
        exact_mod_cast Finset.card_filter_le s (fun i => gap i ≤ t)
      _ ≤ B * Real.exp (A * b) := hb
      _ ≤ B * Real.exp (A * t) := by gcongr

theorem finite_density_exp_sum_le {ι : Type*} (s : Finset ι) (gap : ι → ℝ)
    {M A B u b : ℝ} (hM : 0 < M) (_hA : 0 ≤ A) (hB : 0 ≤ B)
    (hMA : 2 * A ≤ M) (hgap : ∀ i ∈ s, u ≤ gap i)
    (hzero : ∀ i ∈ s, 0 ≤ gap i) (htop : ∀ i ∈ s, gap i ≤ b)
    (hdensity : ∀ t, u ≤ t →
      ((s.filter (fun i => gap i ≤ t)).card : ℝ) ≤ B * Real.exp (A * t)) :
    ∑ i ∈ s, Real.exp (-M * gap i) ≤
      (⌊M * b⌋₊ + 1 : ℝ) * B * Real.exp (1 - M * u / 2) := by
  classical
  let bin : ι → ℕ := fun i => ⌊M * gap i⌋₊
  let bins := Finset.range (⌊M * b⌋₊ + 1)
  have hmap : ∀ i ∈ s, bin i ∈ bins := by
    intro i hi
    apply Finset.mem_range.mpr
    exact Nat.lt_succ_of_le (Nat.floor_mono (mul_le_mul_of_nonneg_left (htop i hi) hM.le))
  rw [← Finset.sum_fiberwise_of_maps_to hmap]
  have hbin : ∀ k ∈ bins,
      ∑ i ∈ s with bin i = k, Real.exp (-M * gap i) ≤
        B * Real.exp (1 - M * u / 2) := by
    intro k hk
    by_cases hempty : (s.filter (fun i => bin i = k)).Nonempty
    · obtain ⟨j, hj⟩ := hempty
      have hjs := (Finset.mem_filter.mp hj).1
      have hjbin := (Finset.mem_filter.mp hj).2
      have hjupper : M * gap j < (k : ℝ) + 1 := by
        simpa only [bin, hjbin] using Nat.lt_floor_add_one (M * gap j)
      have hku : M * u < (k : ℝ) + 1 :=
        lt_of_le_of_lt (mul_le_mul_of_nonneg_left (hgap j hjs) hM.le) hjupper
      have ht : u ≤ ((k : ℝ) + 1) / M := by
        apply (le_div_iff₀ hM).mpr
        nlinarith
      have hsubset : s.filter (fun i => bin i = k) ⊆
          s.filter (fun i => gap i ≤ ((k : ℝ) + 1) / M) := by
        intro i hi
        obtain ⟨his, hik⟩ := Finset.mem_filter.mp hi
        apply Finset.mem_filter.mpr ⟨his, ?_⟩
        apply (le_div_iff₀ hM).mpr
        have hiupper : M * gap i < (k : ℝ) + 1 := by
          simpa only [bin, hik] using Nat.lt_floor_add_one (M * gap i)
        nlinarith
      have hcount : ((s.filter (fun i => bin i = k)).card : ℝ) ≤
          B * Real.exp (A * (((k : ℝ) + 1) / M)) := by
        exact le_trans (by exact_mod_cast Finset.card_le_card hsubset)
          (hdensity _ ht)
      have hexponent : A * (((k : ℝ) + 1) / M) - k ≤ 1 - M * u / 2 := by
        have hkzero : 0 ≤ (k : ℝ) := Nat.cast_nonneg _
        have hhalf : A / M ≤ (1 : ℝ) / 2 := by
          apply (div_le_iff₀ hM).mpr
          linarith
        have hprod := mul_le_mul_of_nonneg_right hhalf (by positivity : 0 ≤ (k : ℝ) + 1)
        rw [div_mul_eq_mul_div] at hprod
        have heq : A * (((k : ℝ) + 1) / M) = A / M * ((k : ℝ) + 1) := by ring
        rw [heq]
        nlinarith
      calc
        ∑ i ∈ s with bin i = k, Real.exp (-M * gap i) ≤
            ∑ _i ∈ s with bin _i = k, Real.exp (-(k : ℝ)) := by
          apply Finset.sum_le_sum
          intro i hi
          obtain ⟨his, hik⟩ := Finset.mem_filter.mp hi
          apply Real.exp_le_exp.mpr
          have hf := Nat.floor_le (mul_nonneg hM.le (hzero i his))
          change (bin i : ℝ) ≤ M * gap i at hf
          rw [hik] at hf
          linarith
        _ = ((s.filter (fun i => bin i = k)).card : ℝ) * Real.exp (-(k : ℝ)) := by
          simp
        _ ≤ (B * Real.exp (A * (((k : ℝ) + 1) / M))) * Real.exp (-(k : ℝ)) := by
          gcongr
        _ = B * Real.exp (A * (((k : ℝ) + 1) / M) - k) := by
          rw [mul_assoc, ← Real.exp_add, sub_eq_add_neg]
        _ ≤ B * Real.exp (1 - M * u / 2) := by gcongr
    · simp only [Finset.not_nonempty_iff_eq_empty.mp hempty, Finset.sum_empty]
      positivity
  calc
    ∑ k ∈ bins, ∑ i ∈ s with bin i = k, Real.exp (-M * gap i) ≤
        ∑ _k ∈ bins, B * Real.exp (1 - M * u / 2) := Finset.sum_le_sum hbin
    _ = (⌊M * b⌋₊ + 1 : ℝ) * B * Real.exp (1 - M * u / 2) := by
      simp [bins, mul_assoc]

end Ostmann.ZeroDensity

end OAI
