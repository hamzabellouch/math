import OAI.NumberTheory.Ostmann.PrimeProgression.CountToHarmonicSupport

namespace OAI

open Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

open scoped BigOperators
namespace Ostmann.Arithmetic.PrimeProgression

noncomputable def closedLogPrimeSupport (M : ℕ) (a : ZMod M) (lo hi : ℝ) : Finset ℕ :=
  (logPrimeSupport ⌊Real.exp hi⌋₊ lo hi).filter fun n : ℕ => (n : ZMod M) = a

lemma mem_closedLogPrimeSupport (M : ℕ) (a : ZMod M) (lo hi : ℝ) (n : ℕ) :
    n ∈ closedLogPrimeSupport M a lo hi ↔
      Real.exp lo ≤ (n : ℝ) ∧ (n : ℝ) ≤ Real.exp hi ∧ n.Prime ∧ (n : ZMod M) = a := by
  classical
  constructor
  · intro hn
    obtain ⟨hs, ha⟩ := Finset.mem_filter.mp hn
    obtain ⟨hnN, hp, hlo, hhi⟩ := (mem_logPrimeSupport _ n lo hi).mp hs
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hp.pos
    exact ⟨(Real.le_log_iff_exp_le hnpos).mp hlo,
      (Real.log_le_iff_le_exp hnpos).mp hhi, hp, ha⟩
  · rintro ⟨hlo, hhi, hp, ha⟩
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hp.pos
    apply Finset.mem_filter.mpr
    refine ⟨(mem_logPrimeSupport _ n lo hi).mpr ⟨?_, hp, ?_, ?_⟩, ha⟩
    · exact (Nat.le_floor_iff (Real.exp_pos hi).le).mpr hhi
    · exact (Real.le_log_iff_exp_le hnpos).mpr hlo
    · exact (Real.log_le_iff_le_exp hnpos).mpr hhi

lemma openLogPrimeSupport_subset_closed (M : ℕ) (a : ZMod M) (lo hi : ℝ) :
    openLogPrimeSupport M a lo hi ⊆ closedLogPrimeSupport M a lo hi := by
  intro n hn
  obtain ⟨hlo, hhi, hp, ha⟩ := (mem_openLogPrimeSupport M a lo hi n).mp hn
  exact (mem_closedLogPrimeSupport M a lo hi n).mpr ⟨hlo.le, hhi, hp, ha⟩

theorem closed_sdiff_open_subset (M : ℕ) (a : ZMod M) (lo hi : ℝ) :
    closedLogPrimeSupport M a lo hi \ openLogPrimeSupport M a lo hi ⊆
      {⌊Real.exp lo⌋₊} := by
  intro n hn
  obtain ⟨hs, hnot⟩ := Finset.mem_sdiff.mp hn
  obtain ⟨hlo, hhi, hp, ha⟩ := (mem_closedLogPrimeSupport M a lo hi n).mp hs
  have hlower : ⌊Real.exp lo⌋₊ ≤ n := by
    simpa only [Nat.floor_natCast] using Nat.floor_le_floor hlo
  have hupper : n ≤ ⌊Real.exp lo⌋₊ := by
    by_contra h
    apply hnot
    apply (mem_openLogPrimeSupport M a lo hi n).mpr
    exact ⟨(Nat.floor_lt (Real.exp_pos lo).le).mp (by omega), hhi, hp, ha⟩
  simp only [Finset.mem_singleton]
  exact le_antisymm hupper hlower

theorem closed_left_endpoint_error (M : ℕ) (a : ZMod M) (lo hi : ℝ) :
    0 ≤ harmonicProgression ⌊Real.exp hi⌋₊ M a lo hi -
        (∑ n ∈ openLogPrimeSupport M a lo hi, (n : ℝ)⁻¹) ∧
      harmonicProgression ⌊Real.exp hi⌋₊ M a lo hi -
        (∑ n ∈ openLogPrimeSupport M a lo hi, (n : ℝ)⁻¹) ≤ Real.exp (-lo) := by
  classical
  let S := closedLogPrimeSupport M a lo hi
  let T := openLogPrimeSupport M a lo hi
  have hsub : T ⊆ S := openLogPrimeSupport_subset_closed M a lo hi
  have hc : (S \ T).card ≤ 1 := by
    simpa only [Finset.card_singleton] using Finset.card_le_card (closed_sdiff_open_subset M a lo hi)
  have hb : (∑ n ∈ S \ T, (n : ℝ)⁻¹) ≤ Real.exp (-lo) := by
    calc
      _ ≤ ∑ _n ∈ S \ T, (Real.exp lo)⁻¹ := by
        apply Finset.sum_le_sum
        intro n hn
        have hnS := (Finset.mem_sdiff.mp hn).1
        have hlo := ((mem_closedLogPrimeSupport M a lo hi n).mp hnS).1
        simpa only [one_div] using one_div_le_one_div_of_le (Real.exp_pos lo) hlo
      _ = ((S \ T).card : ℝ) * (Real.exp lo)⁻¹ := by simp
      _ ≤ 1 * (Real.exp lo)⁻¹ :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hc) (inv_nonneg.mpr (Real.exp_pos lo).le)
      _ = Real.exp (-lo) := by rw [one_mul, Real.exp_neg]
  change 0 ≤ (∑ n ∈ S, (n : ℝ)⁻¹) - (∑ n ∈ T, (n : ℝ)⁻¹) ∧
    (∑ n ∈ S, (n : ℝ)⁻¹) - (∑ n ∈ T, (n : ℝ)⁻¹) ≤ Real.exp (-lo)
  rw [← Finset.sum_sdiff_eq_sub hsub]
  exact ⟨Finset.sum_nonneg (fun n _ => inv_nonneg.mpr (Nat.cast_nonneg n)), hb⟩

end Ostmann.Arithmetic.PrimeProgression

end OAI
