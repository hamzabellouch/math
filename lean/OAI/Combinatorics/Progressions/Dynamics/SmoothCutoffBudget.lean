import OAI.Combinatorics.Progressions.Geometry.BoxChartCutoff
import OAI.Combinatorics.Progressions.Geometry.QuantitativeMetricPartition

namespace OAI

section

namespace Erdos3

open scoped NNReal ContDiff

theorem smooth_cutoff_constant_exp_bound (C a d : ℕ) (hC : 2 ≤ C)
    (A r : ℝ≥0) {p : ℝ} (hA : (A : ℝ) ≤ Real.exp C) (hp : 0 ≤ p) (hd : (d : ℝ) ≤ p)
    (hri : 1 / (r : ℝ) ≤ Real.exp ((p + 2) ^ a)) :
    (((d : ℝ≥0) * A / r : ℝ≥0) : ℝ) ≤ Real.exp ((p + (C + a + 7 : ℕ)) ^ (C + a + 7)) := by
  let T := C + a + 4
  let q := (p + T) ^ T
  have hT : 2 ≤ T := by dsimp [T]; omega
  have hT' : (2 : ℝ) ≤ T := by exact_mod_cast hT
  have hpT : p + T ≤ q := by
    simpa only [pow_one] using pow_le_pow_right₀
      (by linarith : (1 : ℝ) ≤ p + T) (by omega : 1 ≤ T)
  have hCq : (C : ℝ) ≤ q := by
    have hCT : (C : ℝ) ≤ T := by exact_mod_cast (show C ≤ T by dsimp [T]; omega)
    linarith
  have hAq := hA.trans (Real.exp_le_exp.mpr hCq)
  have hdq : (d : ℝ) ≤ Real.exp q := by linarith [Real.add_one_le_exp q]
  have hriq : 1 / (r : ℝ) ≤ Real.exp q := by
    apply hri.trans
    apply Real.exp_le_exp.mpr
    apply (pow_le_pow_left₀ (by linarith) (show p + 2 ≤ p + T by linarith) a).trans
    exact pow_le_pow_right₀ (by linarith) (by dsimp [T]; omega)
  have hprod : ((d : ℝ) * A) * (1 / r) ≤ Real.exp (3 * q) := by
    calc
      _ ≤ (Real.exp q * Real.exp q) * Real.exp q := by gcongr
      _ = _ := by rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
  change (d : ℝ) * A / r ≤ _
  rw [div_eq_mul_one_div]
  apply hprod.trans
  apply Real.exp_le_exp.mpr
  let t : ℝ := p + (T + 3 : ℕ)
  have ht : 3 ≤ t := by dsimp [t]; push_cast; linarith [Nat.cast_nonneg (α := ℝ) T]
  have hqt : q ≤ t ^ T := by
    apply pow_le_pow_left₀ (by positivity)
    dsimp [t]
    push_cast
    linarith
  calc
    3 * q ≤ 3 * t ^ T := by linarith
    _ ≤ t * t ^ T := mul_le_mul_of_nonneg_right ht (by positivity)
    _ = t ^ (T + 1) := (pow_succ' t T).symm
    _ ≤ t ^ (T + 3) := pow_le_pow_right₀ (by linarith) (by omega)
    _ = _ := rfl

theorem exists_smooth_box_cutoffs_exp_bound (a : ℕ) :
    ∃ D : ℕ, 2 ≤ D ∧ ∀ {ι : Type*} [Fintype ι] (p : ℝ) (r : ℝ≥0),
      0 ≤ p → (Fintype.card ι : ℝ) ≤ p → 0 < r → 1 / (r : ℝ) ≤ Real.exp ((p + 2) ^ a) →
      ∃ K : ℝ≥0, (K : ℝ) ≤ Real.exp ((p + D) ^ D) ∧
        ∃ ψ : (ι → ℝ) → ℝ, ContDiff ℝ ∞ ψ ∧ HasCompactSupport ψ ∧
          (∀ v, 0 ≤ ψ v ∧ ψ v ≤ 1) ∧
          (∀ v, (∀ i, |v i| ≤ (r : ℝ) / 2) → ψ v = 1) ∧
          (∀ v, (∃ i, 3 * (r : ℝ) / 4 ≤ |v i|) → ψ v = 0) ∧ LipschitzWith K ψ := by
  obtain ⟨A, _, hcutoff⟩ := exists_smooth_box_cutoffs
  obtain ⟨N, hN⟩ := exists_nat_ge (A : ℝ)
  let C := N + 2
  have hC : 2 ≤ C := by dsimp [C]; omega
  have hA : (A : ℝ) ≤ Real.exp C := by
    have hNC : (N : ℝ) ≤ C := by exact_mod_cast (show N ≤ C by dsimp [C]; omega)
    linarith [Real.add_one_le_exp (C : ℝ)]
  refine ⟨C + a + 7, by omega, ?_⟩
  intro ι _ p r hp hd hr hri
  obtain ⟨ψ, hsmooth, hcompact, hrange, hone, hzero, hLip⟩ := hcutoff (ι := ι) r hr
  exact ⟨Fintype.card ι * A / r, smooth_cutoff_constant_exp_bound C a _ hC A r hA hp hd hri,
    ψ, hsmooth, hcompact, hrange, hone, hzero, hLip⟩

end Erdos3

end

end OAI
