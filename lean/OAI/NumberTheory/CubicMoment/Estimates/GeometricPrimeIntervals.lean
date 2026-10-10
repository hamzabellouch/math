import OAI.NumberTheory.CubicMoment.Estimates.GeometricPrimeBins
import OAI.NumberTheory.CubicMoment.Estimates.PrimeNormEndpoints

namespace OAI

/-! Exact norm intervals for the concrete bins used by the stopping
construction, including their bounded endpoint convention change. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

theorem geometricPrimeBin_eq_iff {ρ B : ℝ} (hρ : 1 < ρ) (hρ₂ : ρ ≤ 2)
    {j : ℕ} (hj : j < geometricBinCount ρ B) {p : Eisenstein}
    (hp : primaryPrime p) (hpB : norm p ≤ B) :
    geometricPrimeBin ρ B p = j ↔
      geometricBinLower ρ B j ≤ norm p ∧ norm p < ρ*geometricBinLower ρ B j := by
  constructor
  · intro he
    simpa only [he] using geometricPrimeBin_cell hρ hρ₂ hp hpB
  · intro hcell
    have hr : 0 < Real.log ρ := Real.log_pos hρ
    have hpn : 0 < norm p := by linarith [primaryPrime_norm_ge_two hp]
    have hn : 0 ≤ Real.log (norm p)/Real.log ρ :=
      div_nonneg (Real.log_nonneg (by linarith [primaryPrime_norm_ge_two hp])) hr.le
    have hlo : ((geometricBinCount ρ B-j:ℕ):ℝ) ≤ Real.log (norm p)/Real.log ρ := by
      apply (le_div_iff₀ hr).mpr
      exact (Real.pow_le_iff_le_log (zero_lt_one.trans hρ) hpn).mp hcell.1
    have hhi : Real.log (norm p)/Real.log ρ < ((geometricBinCount ρ B-j:ℕ):ℝ)+1 := by
      apply (div_lt_iff₀ hr).mpr
      have h : norm p < ρ^(geometricBinCount ρ B-j+1) := by
        simpa only [pow_succ',geometricBinLower] using hcell.2
      simpa only [Nat.cast_add,Nat.cast_one] using
        (Real.lt_pow_iff_log_lt hpn (zero_lt_one.trans hρ)).mp h
    have hf : ⌊Real.log (norm p)/Real.log ρ⌋₊ = geometricBinCount ρ B-j :=
      (Nat.floor_eq_iff hn).mpr ⟨hlo,hhi⟩
    unfold geometricPrimeBin
    rw [hf]
    omega

lemma geometricPrimeBin_away_endpoints {ρ B : ℝ} (hρ : 1 < ρ) (hρ₂ : ρ ≤ 2)
    {j : ℕ} (hj : j < geometricBinCount ρ B) {p : Eisenstein}
    (hp : primaryPrime p) (hpB : norm p ≤ B)
    (hlo : norm p ≠ geometricBinLower ρ B j)
    (hhi : norm p ≠ ρ*geometricBinLower ρ B j) :
    (geometricPrimeBin ρ B p = j) ↔
      geometricBinLower ρ B j < norm p ∧ norm p ≤ ρ*geometricBinLower ρ B j := by
  rw [geometricPrimeBin_eq_iff hρ hρ₂ hj hp hpB]
  constructor
  · rintro ⟨hl,hu⟩
    exact ⟨lt_of_le_of_ne hl hlo.symm,hu.le⟩
  · rintro ⟨hl,hu⟩
    exact ⟨hl.le,lt_of_le_of_ne hu hhi⟩

/-- Replacing a half-open bin by the open-closed interval used by prime
partial summation changes only the two endpoint norms. -/
theorem geometricPrimeBin_endpoint_difference {ρ B : ℝ} (hρ : 1 < ρ) (hρ₂ : ρ ≤ 2)
    {j : ℕ} (hj : j < geometricBinCount ρ B) (S : Finset Eisenstein)
    (hS : ∀ p ∈ S, primaryPrime p ∧ norm p ≤ B)
    (f : Eisenstein → ℂ) {M : ℝ} (hM : 0 ≤ M) (hf : ∀ p ∈ S, ‖f p‖ ≤ M) :
    ‖(∑ p ∈ S with geometricPrimeBin ρ B p = j, f p)-
      (∑ p ∈ S with geometricBinLower ρ B j < norm p ∧
        norm p ≤ ρ*geometricBinLower ρ B j, f p)‖ ≤ 4*M := by
  convert prime_interval_endpoint_difference S (fun p hp => (hS p hp).1)
    (fun p => geometricPrimeBin ρ B p = j)
    (fun p => geometricBinLower ρ B j < norm p ∧ norm p ≤ ρ*geometricBinLower ρ B j)
    (geometricBinLower ρ B j) (ρ*geometricBinLower ρ B j)
    (fun p hp hlo hhi => geometricPrimeBin_away_endpoints hρ hρ₂ hj
      (hS p hp).1 (hS p hp).2 hlo hhi) f hM hf using 1
  congr 2
  all_goals
    apply Finset.sum_congr
    · ext p
      simp only [Finset.mem_filter]
    · intro p hp
      rfl

end CubicFirstMoment

end

end OAI
