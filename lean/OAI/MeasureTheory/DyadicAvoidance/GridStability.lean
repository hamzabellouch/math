import OAI.MeasureTheory.DyadicAvoidance.GridGeometry
import OAI.MeasureTheory.DyadicAvoidance.GridMeasure

namespace OAI

universe u_ι

noncomputable section
namespace Problem310
open MeasureTheory Set

/-- Simultaneous stable centers for a finite list of earlier-grid/later-window pairs. -/
def gridStableCenters {ι : Type u_ι} (a b : ι → ℕ) : Set ℝ :=
  (⋃ i, gridBadCenters ((2 : ℕ) ^ (b i + 2)) (2 * ((2 : ℝ)⁻¹) ^ (a i)))ᶜ

theorem measurableSet_gridStableCenters {ι : Type u_ι} [Countable ι] (a b : ι → ℕ) :
    MeasurableSet (gridStableCenters a b) := by
  apply MeasurableSet.compl
  apply MeasurableSet.iUnion
  intro i
  exact measurableSet_gridBadCenters _ _

theorem gridStableCenters_add_one {ι : Type u_ι} (a b : ι → ℕ) (x : ℝ) :
    x + 1 ∈ gridStableCenters a b ↔ x ∈ gridStableCenters a b := by
  simp only [gridStableCenters, mem_compl_iff, mem_iUnion, not_exists]
  apply forall_congr'
  intro i
  exact not_congr (gridBadCenters_add_one _ (by positivity) _ _)

/-- Stability at a grid also preserves every coarser grid at a later-window trial. -/
theorem gridStableCenters_preserves {ι : Type u_ι} {a b : ι → ℕ} {x t : ℝ}
    (hx : x ∈ gridStableCenters a b) (i : ι) {c n : ℕ}
    (hc : c ≤ b i) (hn : a i ≤ n) (ht : t ∈ Icc (1 : ℝ) 2) :
    dyadicGridKey c (x + t * ((2 : ℝ)⁻¹) ^ n) = dyadicGridKey c x := by
  have hxnot : x ∉ gridBadCenters ((2 : ℕ) ^ (b i + 2))
      (2 * ((2 : ℝ)⁻¹) ^ (a i)) := by
    intro hi
    exact hx (mem_iUnion.mpr ⟨i, hi⟩)
  have hkey := dyadicGridKey_eq_of_stable hn ht (fun k hk ↦ by
    apply hxnot
    apply (mem_gridBadCenters_iff _ _ _).mpr
    exact ⟨k, by simpa using hk⟩)
  rw [← dyadicGridKey_nested hc, ← dyadicGridKey_nested hc, hkey]

private theorem grid_window_width_le {a b : ℕ} (hgap : b + 3 ≤ a) :
    2 * ((2 : ℝ)⁻¹) ^ a ≤ (((2 : ℕ) ^ (b + 2) : ℕ) : ℝ)⁻¹ := by
  have h := pow_right_anti₀ (by norm_num : (0 : ℝ) ≤ 2⁻¹)
    (by norm_num : (2 : ℝ)⁻¹ ≤ 1) hgap
  change (2 : ℝ)⁻¹ ^ a ≤ (2 : ℝ)⁻¹ ^ (b + 3) at h
  have hp : ((2 : ℝ)⁻¹) ^ (b + 3) = ((2 : ℝ)⁻¹) ^ (b + 2) * 2⁻¹ := by
    rw [show b + 3 = (b + 2) + 1 by omega, pow_succ]
  rw [hp] at h
  have h2 : 2 * ((2 : ℝ)⁻¹) ^ a ≤ ((2 : ℝ)⁻¹) ^ (b + 2) := by
    norm_num at h ⊢
    linarith
  simpa only [Nat.cast_pow, Nat.cast_ofNat, inv_pow] using h2

/-- A quantitative simultaneous stability estimate, with no tree assumptions. -/
theorem volume_gridStableCenters_compl_period_le {ι : Type u_ι} [Fintype ι]
    (a b : ι → ℕ) (hgap : ∀ i, b i + 3 ≤ a i) :
    volume ((gridStableCenters a b)ᶜ ∩ Icc (0 : ℝ) 1) ≤
      ENNReal.ofReal (∑ i, (2 : ℝ) ^ (b i + 2) * (2 * ((2 : ℝ)⁻¹) ^ (a i))) := by
  simp only [gridStableCenters, compl_compl]
  simpa using volume_iUnion_gridBadCenters_period_le
    (fun i ↦ (2 : ℕ) ^ (b i + 2)) (fun i ↦ 2 * ((2 : ℝ)⁻¹) ^ (a i))
    (fun i ↦ by positivity) (fun i ↦ by positivity)
    (fun i ↦ grid_window_width_le (hgap i))

/-- The density cost of a gap depends only on its length, not on the grid resolution. -/
theorem dyadic_grid_gap_budget (b g : ℕ) :
    (2 : ℝ) ^ (b + 2) * (2 * ((2 : ℝ)⁻¹) ^ (b + g + 1)) =
      4 * ((2 : ℝ)⁻¹) ^ g := by
  have hcancel : (2 : ℝ) ^ b * ((2 : ℝ)⁻¹) ^ b = 1 := by
    rw [inv_pow]
    exact mul_inv_cancel₀ (by positivity)
  calc
    (2 : ℝ) ^ (b + 2) * (2 * ((2 : ℝ)⁻¹) ^ (b + g + 1))
      = 4 * ((2 : ℝ) ^ b * ((2 : ℝ)⁻¹) ^ b) * ((2 : ℝ)⁻¹) ^ g := by
        simp only [pow_add, pow_one]
        norm_num
        ring
    _ = 4 * ((2 : ℝ)⁻¹) ^ g := by rw [hcancel]; ring

theorem volume_gridStableCenters_compl_gap_le {ι : Type u_ι} [Fintype ι]
    (a b : ι → ℕ) (g : ℕ) (hg : 2 ≤ g)
    (ha : ∀ i, a i = b i + g + 1) :
    volume ((gridStableCenters a b)ᶜ ∩ Icc (0 : ℝ) 1) ≤
      ENNReal.ofReal ((Fintype.card ι : ℝ) * (4 * ((2 : ℝ)⁻¹) ^ g)) := by
  have h := volume_gridStableCenters_compl_period_le a b (fun i ↦ by rw [ha i]; omega)
  have heq : (∑ i, (2 : ℝ) ^ (b i + 2) * (2 * ((2 : ℝ)⁻¹) ^ (a i))) =
      (Fintype.card ι : ℝ) * (4 * ((2 : ℝ)⁻¹) ^ g) := by
    simp only [ha, dyadic_grid_gap_budget, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rwa [heq] at h

/-- The same bound holds when windows are separated by at least the chosen gap.
This can be indexed by all ordered pairs of windows, not just predecessor pairs. -/
theorem volume_gridStableCenters_compl_gap_le_of_le {ι : Type u_ι} [Fintype ι]
    (a b : ι → ℕ) (g : ℕ) (hg : 2 ≤ g)
    (ha : ∀ i, b i + g + 1 ≤ a i) :
    volume ((gridStableCenters a b)ᶜ ∩ Icc (0 : ℝ) 1) ≤
      ENNReal.ofReal ((Fintype.card ι : ℝ) * (4 * ((2 : ℝ)⁻¹) ^ g)) := by
  apply (volume_gridStableCenters_compl_period_le a b (fun i ↦ by have := ha i; omega)).trans
  apply ENNReal.ofReal_le_ofReal
  calc
    (∑ i, (2 : ℝ) ^ (b i + 2) * (2 * ((2 : ℝ)⁻¹) ^ (a i)))
      ≤ ∑ i : ι, 4 * ((2 : ℝ)⁻¹) ^ g := by
        apply Finset.sum_le_sum
        intro i hi
        have hp := pow_right_anti₀ (by norm_num : (0 : ℝ) ≤ 2⁻¹)
          (by norm_num : (2 : ℝ)⁻¹ ≤ 1) (ha i)
        calc
          (2 : ℝ) ^ (b i + 2) * (2 * ((2 : ℝ)⁻¹) ^ (a i))
            ≤ (2 : ℝ) ^ (b i + 2) * (2 * ((2 : ℝ)⁻¹) ^ (b i + g + 1)) := by
              exact mul_le_mul_of_nonneg_left
                (mul_le_mul_of_nonneg_left hp (by norm_num)) (by positivity)
          _ = 4 * ((2 : ℝ)⁻¹) ^ g := dyadic_grid_gap_budget (b i) g
    _ = (Fintype.card ι : ℝ) * (4 * ((2 : ℝ)⁻¹) ^ g) := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/-- Any prescribed finite number of stability conditions has arbitrarily small
exceptional density once the unused gap is sufficiently long. -/
theorem exists_dyadic_gap_budget (K : ℕ) {p : ℝ} (hp : 0 < p) :
    ∃ g : ℕ, 2 ≤ g ∧ (K : ℝ) * (4 * ((2 : ℝ)⁻¹) ^ g) < p := by
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one
    (show 0 < p / (4 * (K + 1 : ℝ)) by positivity)
    (show (2 : ℝ)⁻¹ < 1 by norm_num)
  refine ⟨n + 2, by omega, ?_⟩
  have hpow := pow_right_anti₀ (by norm_num : (0 : ℝ) ≤ 2⁻¹)
    (by norm_num : (2 : ℝ)⁻¹ ≤ 1) (show n ≤ n + 2 by omega)
  change (2 : ℝ)⁻¹ ^ (n + 2) ≤ (2 : ℝ)⁻¹ ^ n at hpow
  have hden : 0 < 4 * (K + 1 : ℝ) := by positivity
  have hlt := (lt_div_iff₀ hden).mp hn
  have hk : (0 : ℝ) ≤ K := Nat.cast_nonneg K
  have hnonneg : 0 ≤ ((2 : ℝ)⁻¹) ^ (n + 2) := by positivity
  nlinarith

end Problem310

end

end OAI
