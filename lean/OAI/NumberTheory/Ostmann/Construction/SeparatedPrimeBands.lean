import OAI.NumberTheory.Ostmann.Construction.SeparatedMassIntervals

namespace OAI

/-! # Separated lower, bulk and upper bands from positive prime mass -/

namespace Ostmann

open Filter
open scoped BigOperators

theorem exists_three_prime_bands {C : ℝ} (hMertens : MertensEstimate C)
    (α β c : ℝ) (hα : 0 < α) (hαβ : α < β) (hc : 0 < c) :
    ∃ q : ℕ, 0 < q ∧ ∀ᶠ L : ℝ in atTop,
      ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime) →
      c * L ≤ weightedIntervalMass P (fun p => Real.log (Real.log p))
        (fun p => (p : ℝ)⁻¹) (α * L) (β * L) →
      ∃ i j k : Fin q, i.val + 1 < j.val ∧ j.val + 1 < k.val ∧
        ∀ t ∈ ({i, j, k} : Finset (Fin q)),
          c * L / (2 * q) ≤
            weightedIntervalMass P (fun p => Real.log (Real.log p))
              (fun p => (p : ℝ)⁻¹)
              (α * L + (t.val : ℝ) * ((β - α) * L / q))
              (α * L + ((t.val : ℝ) + 1) * ((β - α) * L / q)) := by
  let A := Real.exp 1 + 1
  have hA : 0 < A := by dsimp [A]; positivity
  obtain ⟨q, hq⟩ := exists_nat_gt (20 * A * (β - α) / c)
  have hqposR : (0 : ℝ) < q := lt_trans (by positivity) hq
  have hqpos : 0 < q := by exact_mod_cast hqposR
  have hqbound : 20 * A * (β - α) ≤ c * q := by
    have h := (div_lt_iff₀ hc).mp hq
    nlinarith only [h]
  refine ⟨q, hqpos, ?_⟩
  filter_upwards [eventually_gt_atTop (0 : ℝ),
    eventually_ge_atTop (max C 0 / α), eventually_ge_atTop (20 * A / c)] with L hL hLa hLA
  intro P hP hmass
  have ha : max C 0 ≤ α * L := by
    have h := (div_le_iff₀ hα).mp hLa
    nlinarith only [h]
  have hlength : 0 < (β - α) * L := mul_pos (sub_pos.mpr hαβ) hL
  have hroot : c * L ≤
      weightedCDF P (fun p => Real.log (Real.log p)) (fun p => (p : ℝ)⁻¹)
        (α * L + (β - α) * L) -
      weightedCDF P (fun p => Real.log (Real.log p)) (fun p => (p : ℝ)⁻¹) (α * L) := by
    rw [weightedCDF_sub _ _ _ _ _ (by nlinarith)]
    rw [show α * L + (β - α) * L = β * L by ring]
    exact hmass
  have hsize : 10 * (A * (((β - α) * L) / q + 1)) ≤ c * L := by
    have h1 := mul_le_mul_of_nonneg_right hqbound hL.le
    have h2 := (div_le_iff₀ hc).mp hLA
    apply (mul_le_mul_iff_left₀ hqposR).mp
    have he : 10 * (A * (((β - α) * L) / q + 1)) * q =
        10 * A * (β - α) * L + 10 * A * q := by field_simp
    rw [he]
    nlinarith [mul_le_mul_of_nonneg_right h2 hqposR.le]
  obtain ⟨i, j, k, hij, hjk, hm⟩ := three_separated_mass_intervals
    (weightedCDF P (fun p => Real.log (Real.log p)) (fun p => (p : ℝ)⁻¹))
    q hqpos (α * L) ((β - α) * L) (c * L) A hlength hA hroot
    (by
      intro u v hu huv _
      rw [weightedCDF_sub _ _ _ u v huv]
      exact prime_loglog_interval_mass_upper hMertens P hP u v (ha.trans hu) huv) hsize
  refine ⟨i, j, k, hij, hjk, ?_⟩
  intro t ht
  have h := hm t ht
  rw [weightedCDF_sub _ _ _ _ _ (by
    have hq0 : 0 < ((β - α) * L) / q := div_pos hlength hqposR
    nlinarith)] at h
  exact h

end Ostmann

end OAI
