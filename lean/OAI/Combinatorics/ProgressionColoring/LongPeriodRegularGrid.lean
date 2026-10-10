import OAI.Combinatorics.ProgressionColoring.LongPeriodRegularity
import OAI.Combinatorics.ProgressionColoring.RationalGridCount

namespace OAI

/-! The regular-position bound instantiated with the actual shifted rational
grids and their actual integer periods. -/

namespace QuantitativeVanDerWaerden

/-- At least half the positions in a full long-period block are regular.
The coordinate count is proved by the rational-grid theorem, including grid
multiplicity; it is not an assumption of this statement. -/
theorem long_block_regular_card {D h : ℕ} (hh : 0 < h) (hD : 0 < D)
    (rotating : Finset (Fin D)) (Y : Fin h → Fin D → ℝ)
    (y v : Fin D → ℝ) (a : Fin D → ℕ) (η : ℝ) (hη : 0 ≤ η)
    (hpath : ∀ i ∈ rotating, ∀ z, ∃ e : ℤ,
      Y z i - y i - (z.val : ℝ) / h * ((a i : ℝ) + v i) = e)
    (hdrift : ∀ i ∈ rotating, |v i| < η)
    (hperiod : ∀ i ∈ rotating, D ^ 2 < h / Nat.gcd h (a i))
    (hsmall : (D : ℝ) * (4 * η + 1 / (D : ℝ) ^ 2) ≤ 1 / 2) :
    (h : ℝ) / 2 ≤
      ((Finset.univ.filter fun z => ∀ i ∈ rotating, η ≤ rho (Y z i)).card : ℝ) := by
  classical
  let bad : Fin D → Finset (Fin h) := fun i =>
    Finset.univ.filter fun z => rho (Y z i) < η
  have hDpos : (0 : ℝ) < D := by exact_mod_cast hD
  have hcount : ∀ i ∈ rotating, ((bad i).card : ℝ) ≤
      (h : ℝ) * (4 * η + 1 / (D : ℝ) ^ 2) := by
    intro i hi
    let grid : Finset (Fin h) := Finset.univ.filter fun z =>
      rho (y i + (z.val : ℝ) * (a i : ℝ) / h) < 2 * η
    have hsubset : bad i ⊆ grid := by
      intro z hz
      have hbad : rho (Y z i) < η := (Finset.mem_filter.mp hz).2
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ z, ?_⟩
      exact nonregular_implies_grid_near hh z (hpath i hi z) (hdrift i hi) hbad
    have hcard : ((bad i).card : ℝ) ≤ (grid.card : ℝ) := by
      exact_mod_cast Finset.card_le_card hsubset
    have hgrid : (grid.card : ℝ) ≤
        (h : ℝ) * (4 * η + 1 / (h / Nat.gcd h (a i) : ℕ)) :=
      rational_grid_rho_count_le h (a i) hh (y i) η hη
    have hperiodR : (D : ℝ) ^ 2 ≤ (h / Nat.gcd h (a i) : ℕ) := by
      exact_mod_cast (hperiod i hi).le
    have hrec : 1 / ((h / Nat.gcd h (a i) : ℕ) : ℝ) ≤ 1 / (D : ℝ) ^ 2 :=
      one_div_le_one_div_of_le (pow_pos hDpos 2) hperiodR
    exact (hcard.trans hgrid).trans
      (mul_le_mul_of_nonneg_left (by linarith) (Nat.cast_nonneg h))
  rw [regular_positions_eq_complement]
  exact regular_count_of_coordinate_bounds rotating bad (by positivity) hcount hsmall

theorem long_block_regular_card_at_scale {D h : ℕ} (hh : 0 < h) (hD : 3 ≤ D)
    (rotating : Finset (Fin D)) (Y : Fin h → Fin D → ℝ)
    (y v : Fin D → ℝ) (a : Fin D → ℕ)
    (hpath : ∀ i ∈ rotating, ∀ z, ∃ e : ℤ,
      Y z i - y i - (z.val : ℝ) / h * ((a i : ℝ) + v i) = e)
    (hdrift : ∀ i ∈ rotating, |v i| < 1 / (1000 * (D : ℝ)))
    (hperiod : ∀ i ∈ rotating, D ^ 2 < h / Nat.gcd h (a i)) :
    (h : ℝ) / 2 ≤
      ((Finset.univ.filter fun z => ∀ i ∈ rotating,
        1 / (1000 * (D : ℝ)) ≤ rho (Y z i)).card : ℝ) := by
  exact long_block_regular_card hh (by omega) rotating Y y v a _ (by positivity)
    hpath hdrift hperiod (regular_fraction_constant hD)

end QuantitativeVanDerWaerden

end OAI
