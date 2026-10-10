import Mathlib

namespace OAI

universe u_ι

noncomputable section
namespace Problem310
open MeasureTheory Set

/-- Centers whose positive displacement of length `δ` crosses a boundary
of the periodic grid with `q` cells. -/
def gridBadCenters (q : ℕ) (δ : ℝ) : Set ℝ :=
  ⋃ k : ℤ, Ico ((k : ℝ) / q - δ) ((k : ℝ) / q)

theorem mem_gridBadCenters_iff (q : ℕ) (δ x : ℝ) :
    x ∈ gridBadCenters q δ ↔ ∃ k : ℤ, (k : ℝ) / q ∈ Ioc x (x + δ) := by
  simp only [gridBadCenters, mem_iUnion, mem_Ico, mem_Ioc]
  constructor
  · rintro ⟨k, hk⟩
    exact ⟨k, by linarith [hk.1], by linarith [hk.2]⟩
  · rintro ⟨k, hk⟩
    exact ⟨k, by linarith [hk.2], by linarith [hk.1]⟩

theorem measurableSet_gridBadCenters (q : ℕ) (δ : ℝ) :
    MeasurableSet (gridBadCenters q δ) := by
  apply MeasurableSet.iUnion
  intro k
  exact measurableSet_Ico

theorem gridBadCenters_add_one (q : ℕ) (hq : 0 < q) (δ x : ℝ) :
    x + 1 ∈ gridBadCenters q δ ↔ x ∈ gridBadCenters q δ := by
  rw [mem_gridBadCenters_iff, mem_gridBadCenters_iff]
  have hq0 : (q : ℝ) ≠ 0 := by positivity
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨k - q, ?_⟩
    have he : ((k - q : ℤ) : ℝ) / q = (k : ℝ) / q - 1 := by
      push_cast
      field_simp
    rw [he]
    exact ⟨by linarith [hk.1], by linarith [hk.2]⟩
  · rintro ⟨k, hk⟩
    refine ⟨k + q, ?_⟩
    have he : ((k + q : ℤ) : ℝ) / q = (k : ℝ) / q + 1 := by
      push_cast
      field_simp
    rw [he]
    exact ⟨by linarith [hk.1], by linarith [hk.2]⟩

/-- Inside a half-open period the bad centers are covered by exactly `q`
intervals of length `δ`, provided `δ` is at most one cell width. -/
theorem gridBadCenters_period_subset (q : ℕ) (hq : 0 < q) {δ : ℝ}
    (hδ : δ ≤ (q : ℝ)⁻¹) :
    gridBadCenters q δ ∩ Ico (0 : ℝ) 1 ⊆
      ⋃ i : Fin q, Ico (((i.val + 1 : ℕ) : ℝ) / q - δ)
        (((i.val + 1 : ℕ) : ℝ) / q) := by
  intro x hx
  obtain ⟨k, hk⟩ := (mem_gridBadCenters_iff q δ x).mp hx.1
  have hqpos : (0 : ℝ) < q := by exact_mod_cast hq
  have hkpos : 0 < k := by
    have : (0 : ℝ) < (k : ℝ) / q := lt_of_le_of_lt hx.2.1 hk.1
    have := (div_pos_iff.mp this)
    exact_mod_cast (by rcases this with h | h; exact h.1; linarith [h.2] : (0 : ℝ) < k)
  have hklt : k < (q : ℤ) + 1 := by
    have hstep : (k : ℝ) / q < 1 + (q : ℝ)⁻¹ := by linarith [hx.2.2, hk.2]
    have hmul := (div_lt_iff₀ hqpos).mp hstep
    have hi : (q : ℝ)⁻¹ * q = 1 := inv_mul_cancel₀ hqpos.ne'
    have : (k : ℝ) < q + 1 := by nlinarith
    exact_mod_cast this
  have hkq : k.toNat ≤ q := by omega
  have hkn : 0 < k.toNat := by omega
  let i : Fin q := ⟨k.toNat - 1, by omega⟩
  apply mem_iUnion.mpr
  refine ⟨i, ?_⟩
  have hki : ((i.val + 1 : ℕ) : ℝ) = (k : ℝ) := by
    have : i.val + 1 = k.toNat := by dsimp [i]; omega
    rw [this]
    exact_mod_cast (Int.toNat_of_nonneg hkpos.le)
  rw [hki]
  exact ⟨by linarith [hk.2], hk.1⟩

theorem volume_gridBadCenters_period_le (q : ℕ) (hq : 0 < q) {δ : ℝ}
    (_hδ0 : 0 ≤ δ) (hδ : δ ≤ (q : ℝ)⁻¹) :
    volume (gridBadCenters q δ ∩ Icc (0 : ℝ) 1) ≤ ENNReal.ofReal ((q : ℝ) * δ) := by
  have hae : (gridBadCenters q δ ∩ Icc (0 : ℝ) 1 : Set ℝ) =ᵐ[volume]
      (gridBadCenters q δ ∩ Ico (0 : ℝ) 1 : Set ℝ) := by
    exact Filter.EventuallyEqSet.inter Filter.EventuallyEq.rfl
      (Ico_ae_eq_Icc (μ := volume) (a := (0 : ℝ)) (b := 1)).symm
  rw [measure_congr hae]
  calc
    volume (gridBadCenters q δ ∩ Ico (0 : ℝ) 1)
      ≤ volume (⋃ i : Fin q, Ico (((i.val + 1 : ℕ) : ℝ) / q - δ)
          (((i.val + 1 : ℕ) : ℝ) / q)) :=
        measure_mono (gridBadCenters_period_subset q hq hδ)
    _ ≤ ∑ i : Fin q, volume (Ico (((i.val + 1 : ℕ) : ℝ) / q - δ)
          (((i.val + 1 : ℕ) : ℝ) / q)) := measure_iUnion_fintype_le _ _
    _ = ENNReal.ofReal ((q : ℝ) * δ) := by
      simp only [Real.volume_Ico, sub_sub_cancel]
      simp [ENNReal.ofReal_mul]

/-- The exceptional density for any finite family of stability requirements
is bounded by the sum of its grid-width budgets. -/
theorem volume_iUnion_gridBadCenters_period_le {ι : Type u_ι} [Fintype ι]
    (q : ι → ℕ) (δ : ι → ℝ) (hq : ∀ i, 0 < q i)
    (hδ0 : ∀ i, 0 ≤ δ i) (hδ : ∀ i, δ i ≤ (q i : ℝ)⁻¹) :
    volume ((⋃ i, gridBadCenters (q i) (δ i)) ∩ Icc (0 : ℝ) 1) ≤
      ENNReal.ofReal (∑ i, (q i : ℝ) * δ i) := by
  classical
  rw [iUnion_inter]
  calc
    volume (⋃ i, gridBadCenters (q i) (δ i) ∩ Icc (0 : ℝ) 1)
      ≤ ∑ i, volume (gridBadCenters (q i) (δ i) ∩ Icc (0 : ℝ) 1) :=
        measure_iUnion_fintype_le _ _
    _ ≤ ∑ i, ENNReal.ofReal ((q i : ℝ) * δ i) := by
      apply Finset.sum_le_sum
      intro i hi
      exact volume_gridBadCenters_period_le (q i) (hq i) (hδ0 i) (hδ i)
    _ = ENNReal.ofReal (∑ i, (q i : ℝ) * δ i) := by
      symm
      apply ENNReal.ofReal_sum_of_nonneg
      intro i hi
      exact mul_nonneg (Nat.cast_nonneg _) (hδ0 i)

end Problem310

end

end OAI
