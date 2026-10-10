import OAI.NumberTheory.EgyptianFractions.SmallPrimeSelectedClass
import OAI.NumberTheory.EgyptianFractions.DivisorClasses
import OAI.NumberTheory.EgyptianFractions.DivisorPointwiseUniform
import OAI.NumberTheory.EgyptianFractions.IntermediateBandDecay

namespace OAI
noncomputable section
open Filter Topology
open scoped BigOperators
namespace Problem337.DivisorMoment
attribute [local instance] Classical.propDecidable

/-- Complete small-prime contribution, including the actual class, pointwise
weight control, and exponential loss absorption. -/
theorem small_class_truncated_moment_bound (D r : ℝ) (hD : 1 ≤ D) (hr : 0 ≤ r) :
    ∀ᶠ S : ℝ in atTop, ∀ X Y : ℝ, ∀ N : ℕ,
      S / (2 * Real.log S) ≤ Real.log X →
      Real.log X ≤ D * S → Real.sqrt X ≤ Y → Y ≤ X →
      (N : ℝ) ≤ Real.exp (D * S) →
      (∑ h ∈ Finset.Icc 1 ⌊Y⌋₊ with
          DivisorClasses.SmallClass (N + h) S (Real.log X) Y,
        (truncatedDivisorCount X (N + h) : ℝ) ^ r) ≤
        2 * Y * Real.exp (-Real.log X / 100) := by
  obtain ⟨C, _hC, hclass⟩ := small_prime_selected_prefix_sum_bound
  obtain ⟨S0, hpoint⟩ := truncatedDivisorCount_shifted_uniform_subpower
    D r (1 / 200) hD hr (by norm_num)
  filter_upwards [hclass, eventually_small_rankin_exponent_le C,
    eventually_ge_atTop S0, eventually_ge_atTop (2 : ℝ)] with S hclass habs hS0 hS2
  intro X Y N hlo hhi hXY hYX hN
  have hSpos : 0 < S := by linarith
  have hlogS : 0 < Real.log S := Real.log_pos (by linarith)
  have hlogX : 0 < Real.log X := (by positivity : 0 < S / (2 * Real.log S)).trans_le hlo
  have hXnonneg : 0 ≤ X := (Real.sqrt_nonneg X).trans (hXY.trans hYX)
  have hX : 1 < X := (Real.log_pos_iff hXnonneg).mp hlogX
  have hXpos : 0 < X := by linarith
  have hsqrt1 : 1 ≤ Real.sqrt X := by
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hX.le
  have hY : 1 ≤ Y := hsqrt1.trans hXY
  have hYpos : 0 < Y := by linarith
  have hYlog : Real.log X / 2 ≤ Real.log Y := by
    have h := Real.log_le_log (Real.sqrt_pos.mpr hXpos) hXY
    simpa only [Real.log_sqrt hXnonneg] using h
  let A : Finset ℕ := (Finset.Icc 1 ⌊Y⌋₊).filter
    (fun h => DivisorClasses.SmallClass (N + h) S (Real.log X) Y)
  have hA : A ⊆ Finset.Icc 1 ⌊Y⌋₊ := Finset.filter_subset _ _
  have hw : ∀ h ∈ A, (truncatedDivisorCount X (N + h) : ℝ) ^ r ≤
      Real.exp ((1 / 200 : ℝ) * Real.log X) := by
    intro h hh
    obtain ⟨hh1, hhY⟩ := Finset.mem_Icc.mp (hA hh)
    have hhYR : (h : ℝ) ≤ Y :=
      (by exact_mod_cast hhY : (h : ℝ) ≤ ⌊Y⌋₊).trans (Nat.floor_le hYpos.le)
    exact hpoint S hS0 X Y N h hX.le hlo hhi hN hh1 hhYR hYX
  have hpfx : ∀ h ∈ A, ∃ d p : ℕ, 0 < d ∧ 0 < p ∧ d ∣ N + h ∧
      (d : ℝ) ≤ Real.sqrt Y ∧ Real.sqrt Y < (d : ℝ) * p ∧
      (∀ ℓ : ℕ, ℓ.Prime → ℓ ∣ d → ℓ ≤ p) ∧
      Real.log (p : ℝ) < Real.log X ^ (15 / 16 : ℝ) ∧
      Real.log (p : ℝ) < 4 * Real.log S := by
    intro h hh
    obtain ⟨d, p, hpref, hplarge, hpsmall⟩ := (Finset.mem_filter.mp hh).2
    obtain ⟨hd, hp, hdvd, hdY, hcross, _hpdvd, hpf, _hrf⟩ := hpref
    exact ⟨d, p, hd, hp.pos, hdvd, hdY,
      by simpa only [Nat.cast_mul] using hcross, hpf, hplarge, hpsmall⟩
  have hbound := hclass (Real.log X) ((1 / 200 : ℝ) * Real.log X) Y hlo hY hYlog
    N A (fun n => (truncatedDivisorCount X n : ℝ) ^ r) hA hw hpfx
  have hexp := habs (Real.log X) ((1 / 200 : ℝ) * Real.log X) hlo
    (by ring_nf; exact le_rfl)
  exact hbound.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexp)
    (by positivity))

end Problem337.DivisorMoment

end

end OAI
