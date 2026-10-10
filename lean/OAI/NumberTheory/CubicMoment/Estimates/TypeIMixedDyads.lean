import OAI.NumberTheory.CubicMoment.Estimates.TypeIMixedPrime

namespace OAI

/-! A fixed number of relative norm dyads covers the full product support.
The number is independent of the product length. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def typeIMixedDyadIndex (L : ℝ) (r : Eisenstein) : ℕ :=
  if h : 1 ≤ norm r/L then Classical.choose (exists_nat_pow_near h (by norm_num : (1:ℝ) < 2)) else 0

def typeIMixedDyad (S : Finset Eisenstein) (L : ℝ) (j : ℕ) : Finset Eisenstein :=
  S.filter (fun r => typeIMixedDyadIndex L r = j)

lemma typeIMixedDyadIndex_bounds {L : ℝ} (hL : 0 < L) {r : Eisenstein}
    (hr : L ≤ norm r) :
    L*(2:ℝ)^typeIMixedDyadIndex L r ≤ norm r ∧
      norm r < 2*(L*(2:ℝ)^typeIMixedDyadIndex L r) := by
  have hratio : 1 ≤ norm r/L := (le_div_iff₀ hL).mpr (by simpa using hr)
  have hb := Classical.choose_spec (exists_nat_pow_near hratio (by norm_num : (1:ℝ) < 2))
  unfold typeIMixedDyadIndex
  rw [dite_eq_left hratio]
  constructor
  · simpa only [mul_comm] using (le_div_iff₀ hL).mp hb.1
  · have hh := (div_lt_iff₀ hL).mp hb.2
    rw [pow_succ] at hh
    nlinarith

lemma typeIMixedDyadIndex_lt {L D : ℝ} {J : ℕ} (hL : 0 < L) (hD : D < (2:ℝ)^J)
    {r : Eisenstein} (hr : L ≤ norm r) (hrD : norm r ≤ D*L) :
    typeIMixedDyadIndex L r < J := by
  apply (pow_right_strictMono₀ (by norm_num : (1:ℝ) < 2)).lt_iff_lt.mp
  have hb := (typeIMixedDyadIndex_bounds hL hr).1
  nlinarith [mul_lt_mul_of_pos_right hD hL]

lemma typeIMixedDyad_partition (S : Finset Eisenstein) {L D : ℝ} {J : ℕ}
    (hL : 0 < L) (hD : D < (2:ℝ)^J)
    (hS : ∀ r ∈ S, L ≤ norm r ∧ norm r ≤ D*L) (f : Eisenstein → ℂ) :
    (∑ r ∈ S, f r) = ∑ j ∈ Finset.range J, ∑ r ∈ typeIMixedDyad S L j, f r := by
  exact (Finset.sum_fiberwise_of_maps_to (fun r hr =>
    Finset.mem_range.mpr (typeIMixedDyadIndex_lt hL hD (hS r hr).1 (hS r hr).2)) f).symm

end CubicFirstMoment

end

end OAI
