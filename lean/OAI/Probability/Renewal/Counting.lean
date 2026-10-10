import OAI.Probability.Renewal.Definitions

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal
namespace HoneycombLocal

def indexWindow (x r : ℝ) : Finset ℕ := Finset.Icc ⌈x⌉₊ ⌊(1 + r) * x⌋₊

lemma mem_indexWindow {x r : ℝ} (hx : 0 ≤ x) (hr : 0 ≤ r) {k : ℕ}
    (hk : k ∈ indexWindow x r) : x ≤ (k : ℝ) ∧ (k : ℝ) ≤ (1 + r) * x := by
  obtain ⟨hl, hu⟩ := Finset.mem_Icc.mp hk
  exact ⟨(Nat.le_ceil x).trans (by exact_mod_cast hl),
    (by exact_mod_cast hu : (k : ℝ) ≤ (⌊(1 + r) * x⌋₊ : ℝ)).trans (Nat.floor_le (by positivity))⟩

lemma card_indexWindow {x r : ℝ} (hx : 0 ≤ x) (_hr : 0 ≤ r) (hrx : 2 ≤ r * x) :
    r * x / 2 ≤ ((indexWindow x r).card : ℝ) := by
  have hceil := Nat.ceil_lt_add_one hx
  have hfloor := Nat.lt_floor_add_one ((1 + r) * x)
  have hcf : ⌈x⌉₊ ≤ ⌊(1 + r) * x⌋₊ := Nat.le_floor (by nlinarith)
  rw [indexWindow, Nat.card_Icc, Nat.cast_sub (hcf.trans (Nat.le_succ _)), Nat.cast_succ]
  nlinarith

lemma renewalMass_eq_tsum (p : PMF ℕ) {m : ℕ} (hm : 0 < m) :
    renewalMass p m = ∑' k : ℕ, sumLaw p k m := by
  rw [tsum_eq_zero_add' ENNReal.summable]
  simp [sumLaw, PMF.pure_apply, hm.ne', renewalMass]

lemma renewal_lower_finset (p : PMF ℕ) {m : ℕ} (hm : 0 < m) (s : Finset ℕ) {b : ℝ}
    (hb : ∀ k ∈ s, b ≤ (sumLaw p k m).toReal) :
    ENNReal.ofReal (b * (s.card : ℝ)) ≤ renewalMass p m := by
  calc
    ENNReal.ofReal (b * (s.card : ℝ)) = ENNReal.ofReal (∑ _k ∈ s, b) := by simp [mul_comm]
    _ ≤ ENNReal.ofReal (∑ k ∈ s, (sumLaw p k m).toReal) :=
      ENNReal.ofReal_le_ofReal (Finset.sum_le_sum hb)
    _ = ∑ k ∈ s, sumLaw p k m := by
      rw [ENNReal.ofReal_sum_of_nonneg (fun _ _ => ENNReal.toReal_nonneg)]
      simp only [ENNReal.ofReal_toReal (PMF.apply_ne_top _ _)]
    _ ≤ renewalMass p m := by rw [renewalMass_eq_tsum p hm]; exact ENNReal.sum_le_tsum s

lemma inverse_tilt_scale {a A m : ℝ} (hA : 0 < A) (hm : 0 < m) :
    m / (A / m) ^ (a - 1) = A ^ (1 - a) * m ^ a := by
  rw [Real.div_rpow hA.le hm.le, div_div_eq_mul_div]
  have hM : m * m ^ (a - 1) = m ^ a := by
    have hh := Real.rpow_add_one hm.ne' (a - 1)
    simp only [sub_add_cancel] at hh
    simpa only [mul_comm] using hh.symm
  rw [hM]
  have hA' : A ^ (1 - a) = (A ^ (a - 1))⁻¹ := by
    rw [show (1 - a : ℝ) = -(a - 1) by ring, Real.rpow_neg hA.le]
  rw [hA']
  ring

end HoneycombLocal

end

end OAI
