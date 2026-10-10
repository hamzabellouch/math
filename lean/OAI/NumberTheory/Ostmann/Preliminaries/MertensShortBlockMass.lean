import OAI.NumberTheory.Ostmann.Construction.LogCellFamilyWindow
import OAI.NumberTheory.Ostmann.Preliminaries.MertensPrimeBands

namespace OAI

/-! # Mertens bounds for the complete giant cell family -/

namespace Ostmann
open scoped Classical BigOperators

theorem mertens_log_block_upper {C : ℝ} (hM : MertensEstimate C)
    (S : Finset ℕ) (s t : ℝ) (hs : 1 ≤ s) (hst : s ≤ t)
    (hS : ∀ p ∈ S, p.Prime ∧ s < Real.log p ∧ Real.log p ≤ t) :
    (∑ p ∈ S, Real.log (p : ℝ) / p) ≤ t - s + Real.log 2 + 2 * C := by
  let D := Nat.primesLE ⌊Real.exp t⌋₊ \ Nat.primesLE ⌊Real.exp s⌋₊
  have hsub : S ⊆ D := by
    intro p hp
    obtain ⟨hprime, hlo, hhi⟩ := hS p hp
    have hp0 : (0 : ℝ) < p := Nat.cast_pos.mpr hprime.pos
    apply Finset.mem_sdiff.mpr
    constructor
    · apply Nat.mem_primesLE.mpr
      exact ⟨Nat.le_floor ((Real.log_le_iff_le_exp hp0).mp hhi), hprime⟩
    · intro hh
      have hle : (p : ℝ) ≤ Real.exp s :=
        (Nat.cast_le.mpr (Nat.le_of_mem_primesLE hh)).trans (Nat.floor_le (Real.exp_nonneg _))
      exact (not_le_of_gt hlo) ((Real.log_le_iff_le_exp hp0).mpr hle)
  have hnest : Nat.primesLE ⌊Real.exp s⌋₊ ⊆ Nat.primesLE ⌊Real.exp t⌋₊ := by
    intro p hp
    exact Nat.mem_primesLE.mpr ⟨(Nat.le_of_mem_primesLE hp).trans
      (Nat.floor_mono (Real.exp_le_exp.mpr hst)), Nat.prime_of_mem_primesLE hp⟩
  have hupper := hM.upper _ (floor_exp_log_bounds t (hs.trans hst)).1
  have hlower := hM.lower _ (floor_exp_log_bounds s hs).1
  calc
    _ ≤ ∑ p ∈ D, Real.log (p : ℝ) / p :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun p _ _ =>
        div_nonneg (Real.log_natCast_nonneg _) (Nat.cast_nonneg _))
    _ = (∑ p ∈ Nat.primesLE ⌊Real.exp t⌋₊, Real.log (p : ℝ) / p) -
        ∑ p ∈ Nat.primesLE ⌊Real.exp s⌋₊, Real.log (p : ℝ) / p :=
      Finset.sum_sdiff_eq_sub hnest
    _ ≤ _ := by linarith [(floor_exp_log_bounds t (hs.trans hst)).2.2,
      (floor_exp_log_bounds s hs).2.1]

/-- The total mass of all complete cells near the block is of order its
length divided by its location, including the overlapping boundary cells. -/
theorem logBlock_family_mass_upper {C : ℝ} (hM : MertensEstimate C)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (lo hi : ℝ)
    (hlo : 5 ≤ lo) (hlohi : lo ≤ hi) :
    (∑ p ∈ P, (p : ℝ)⁻¹ * logCellFamilyWeight (logBlockCenters lo hi) p) ≤
      (hi - lo + 8 + Real.log 2 + 2 * C) / (lo - 4) := by
  let Q := P.filter (fun p => logCellFamilyWeight (logBlockCenters lo hi) p ≠ 0)
  have hQ (p : ℕ) (hp : p ∈ Q) :
      p.Prime ∧ lo - 4 < Real.log p ∧ Real.log p ≤ hi + 4 := by
    obtain ⟨hpP, hn⟩ := Finset.mem_filter.mp hp
    have hr : lo - 3 ≤ Real.log p ∧ Real.log p ≤ hi + 3 := by
      constructor
      · by_contra! hh
        exact hn (logBlockCenters_weight_zero lo hi p (Or.inl hh))
      · by_contra! hh
        exact hn (logBlockCenters_weight_zero lo hi p (Or.inr hh))
    exact ⟨hP p hpP, by linarith [hr.1], by linarith [hr.2]⟩
  have he : (∑ p ∈ P, (p : ℝ)⁻¹ * logCellFamilyWeight (logBlockCenters lo hi) p) =
      ∑ p ∈ Q, (p : ℝ)⁻¹ * logCellFamilyWeight (logBlockCenters lo hi) p := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro p hp hn
    have hz : logCellFamilyWeight (logBlockCenters lo hi) p = 0 := by
      simpa only [Q, Finset.mem_filter, hp, true_and, not_not] using hn
    rw [hz, mul_zero]
  have hw := mertens_log_block_upper hM Q (lo - 4) (hi + 4)
    (by linarith) (by linarith) hQ
  rw [he]
  apply (le_div_iff₀ (by linarith : 0 < lo - 4)).mpr
  calc
    _ = ∑ p ∈ Q, (lo - 4) * (p : ℝ)⁻¹ * logCellFamilyWeight (logBlockCenters lo hi) p := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro p _
      ring
    _ ≤ ∑ p ∈ Q, Real.log (p : ℝ) / p := by
      apply Finset.sum_le_sum
      intro p hp
      have h1 := logCellFamilyWeight_le_one (logBlockCenters lo hi) p
      have h0 := logCellFamilyWeight_nonneg (logBlockCenters lo hi) p
      calc
        _ ≤ (lo - 4) * (p : ℝ)⁻¹ :=
          mul_le_of_le_one_right (mul_nonneg (by linarith) (by positivity)) h1
        _ ≤ Real.log (p : ℝ) / p := by
          simpa only [div_eq_mul_inv] using
            mul_le_mul_of_nonneg_right (hQ p hp).2.1.le (by positivity : 0 ≤ (p : ℝ)⁻¹)
    _ ≤ _ := by linarith

/-- Localized harmonic weights fit directly under the logarithmic collision
budget. The zero-weight primes in the large container need no lower bound. -/
theorem logBlock_family_collision_weight (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (lo hi : ℝ) (hlo : 4 < lo) (p : P) :
    ((p : ℝ)⁻¹ * logCellFamilyWeight (logBlockCenters lo hi) p) * (p : ℝ) ≤
      Real.log (p : ℝ) / (lo - 4) := by
  have hp0 : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (hP p p.property).ne_zero
  rw [mul_right_comm, inv_mul_cancel₀ hp0, one_mul]
  by_cases hz : logCellFamilyWeight (logBlockCenters lo hi) p = 0
  · rw [hz]
    exact div_nonneg (Real.log_natCast_nonneg _) (by linarith)
  · have hl : lo - 3 ≤ Real.log (p : ℝ) := by
      by_contra! hh
      exact hz (logBlockCenters_weight_zero lo hi p (Or.inl hh))
    exact (logCellFamilyWeight_le_one _ _).trans
      ((le_div_iff₀ (by linarith : 0 < lo - 4)).mpr (by linarith))

end Ostmann

end OAI
