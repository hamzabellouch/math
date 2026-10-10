import OAI.NumberTheory.Ostmann.Characters.CharacterBandGeometry
import OAI.NumberTheory.Ostmann.Construction.RichGridShell
import OAI.NumberTheory.Ostmann.Construction.TargetPrimeWords

namespace OAI

/-! # The lower shell, bulk band and rich upper block are selected together -/
namespace Ostmann
open Filter
open scoped Classical BigOperators

theorem exists_character_band_selection {C : ℝ} (hM : MertensEstimate C)
    (α β c : ℝ) (hα : 0 < α) (hαβ : α < β) (hc : 0 < c) :
    ∃ q : ℕ, 0 < q ∧ ∃ H : ℕ, ∀ K : ℕ, 1 ≤ K →
      4 ≤ (1 / 10000 : ℝ) * K →
      64 * (Real.exp 1 + 1) ≤ (c / (2 * (β - α))) * (1 / 10000 : ℝ) * K →
      ∀ᶠ L : ℝ in atTop, ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime) →
      c * L ≤ weightedIntervalMass P (fun p => Real.log (Real.log p))
        (fun p => (p : ℝ)⁻¹) (α * L) (β * L) →
      let width := ((β - α) / q) * L
      ∃ i j k : Fin q, i.val + 1 < j.val ∧ j.val + 1 < k.val ∧
        c * L / (2 * q) ≤ weightedIntervalMass P (fun p => Real.log (Real.log p))
          (fun p => (p : ℝ)⁻¹) (characterBandPoint α β q j.val * L)
          (characterBandPoint α β q j.val * L + width) ∧
        ∃ us : ℝ, characterBandPoint α β q i.val * L ≤ us ∧
          us + 1 ≤ characterBandPoint α β q i.val * L + width ∧
          c / (32 * (β - α)) ≤ ∑ p ∈ loglogShell P us, (p : ℝ)⁻¹ ∧
        ∃ h : ℕ, h ≤ H ∧ ∃ U : ℝ,
          characterBandPoint α β q k.val * L ≤ U ∧
          U + 5 * (K * 200000 ^ h : ℕ) ≤ characterBandPoint α β q k.val * L + width ∧
          ∀ u v : ℝ, U ≤ u → v ≤ U + 5 * (K * 200000 ^ h : ℕ) →
            ((K * 200000 ^ h : ℕ) : ℝ) / 10000 ≤ v - u →
            ∃ t : ℕ, u ≤ U + t ∧ U + t + 1 ≤ v ∧
              c / (32 * (β - α)) ≤ ∑ p ∈ loglogShell P (U + t), (p : ℝ)⁻¹ := by
  obtain ⟨q, hq, hbands⟩ := exists_three_prime_bands hM α β c hα hαβ hc
  let d := c / (2 * (β - α))
  have hd : 0 < d := by dsimp [d]; positivity
  let A := Real.exp 1 + 1
  have hA : 0 < A := by dsimp [A]; positivity
  obtain ⟨H, hr⟩ := exists_rich_prime_grid_block hM 200000 (by norm_num)
    d (1 / 10000) hd (by norm_num) (by norm_num)
  refine ⟨q, hq, H, ?_⟩
  intro K hK hKε hKA
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hw : 0 < (β - α) / q := div_pos (sub_pos.mpr hαβ) hqR
  have hwidth := tendsto_id.const_mul_atTop hw
  have hstart := tendsto_id.const_mul_atTop hα
  filter_upwards [hbands, eventually_gt_atTop (0 : ℝ),
    hstart.eventually (eventually_ge_atTop (max C 0)),
    hwidth.eventually (eventually_ge_atTop 4),
    hwidth.eventually (eventually_ge_atTop (8 * A / d)),
    hwidth.eventually (eventually_gt_atTop (2 * A * (5 * K * (200000 : ℝ) ^ H + 1) / d))]
    with L hbands hL hstart hwidth4 hwidthmass hwidthlarge
  intro P hP hmass width
  obtain ⟨i, j, k, hij, hjk, hm⟩ := hbands P hP hmass
  have hwidth4' : 4 ≤ width := hwidth4
  have hwidth0 : 0 ≤ width := le_trans (by norm_num) hwidth4
  have hwidthmass' : 8 * A ≤ d * width := by
    have hh := (div_le_iff₀ hd).mp hwidthmass
    exact hh.trans_eq (mul_comm _ _)
  have hlarge : 2 * A * (5 * K * (200000 : ℝ) ^ H + 1) < d * width := by
    have hh := (div_lt_iff₀ hd).mp hwidthlarge
    exact hh.trans_eq (mul_comm _ _)
  have he : d * width = c * L / (2 * q) := by
    dsimp [d, width]
    field_simp [ne_of_gt (sub_pos.mpr hαβ), ne_of_gt hqR]
  have hcell (t : Fin q) (ht : t ∈ ({i, j, k} : Finset (Fin q))) :
      d * width ≤ weightedIntervalMass P (fun p => Real.log (Real.log p))
        (fun p => (p : ℝ)⁻¹) (characterBandPoint α β q t.val * L)
          (characterBandPoint α β q t.val * L + width) := by
    rw [he]
    convert hm t ht using 2 <;> dsimp [characterBandPoint, width] <;> ring
  have hbase (t : Fin q) : max C 0 ≤ characterBandPoint α β q t.val * L := by
    exact hstart.trans (mul_le_mul_of_nonneg_right
      (characterBandPoint_bounds α β q t.val hαβ hq (by omega)).1 hL.le)
  let ai := characterBandPoint α β q i.val * L
  let ak := characterBandPoint α β q k.val * L
  let φ := weightedCDF P (fun p => Real.log (Real.log p)) (fun p => (p : ℝ)⁻¹)
  have hmono : Monotone φ := weightedCDF_mono _ _ _ (by intros; positivity)
  have hsmall : d * width ≤ φ (ai + width) - φ ai := by
    rw [weightedCDF_sub _ _ _ ai (ai + width) (by linarith only [hwidth0])]
    exact hcell i (by simp)
  obtain ⟨s, hslo, hshi, hsmass⟩ := exists_rich_grid_shell φ hmono ai A d ai (ai + width)
    hA hd.le le_rfl (by linarith only [hwidth4']) (by linarith only [hwidthmass'])
    (fun a ha => by
      rw [weightedCDF_sub _ _ _ a (a + 1) (by linarith)]
      exact prime_loglog_unit_mass_upper hM P hP a ((hbase i).trans ha))
    (by simpa only [add_sub_cancel_left] using hsmall)
  obtain ⟨h, U, hh, hUlo, hUhi, hrich⟩ := hr K hK hKε hKA P hP ak width (hbase k)
    hwidth0 hlarge (hcell k (by simp))
  have hcost : c / (32 * (β - α)) = d / 16 := by
    dsimp [d]
    field_simp [ne_of_gt (sub_pos.mpr hαβ)]
    ring
  refine ⟨i, j, k, hij, hjk, ?_, ai + s, hslo, hshi, ?_, h, hh, U, hUlo, ?_, ?_⟩
  · rw [← he]
    exact hcell j (by simp)
  · rw [weightedCDF_sub _ _ _ (ai + s) (ai + s + 1) (by linarith)] at hsmass
    rw [hcost]
    exact (by linarith only [hd] : d / 16 ≤ d / 2).trans hsmass
  · simpa only [Nat.cast_mul, Nat.cast_pow, mul_assoc] using hUhi
  · intro u v hu hv hlen
    obtain ⟨t, htlo, hthi, htmass⟩ := hrich u v hu
      (by simpa only [Nat.cast_mul, Nat.cast_pow, mul_assoc] using hv)
      (by
        convert hlen using 1
        push_cast
        ring)
    refine ⟨t, htlo, hthi, ?_⟩
    rw [hcost]
    exact htmass

end Ostmann

end OAI
