import OAI.MeasureTheory.Falconer.Estimates.ScalarGroupedTreeGain
import Mathlib.Algebra.BigOperators.Intervals

namespace OAI

/-! Minimal heavy suffixes for the porous level-bunching construction.
 Trimming a short terminal segment has a controlled entropy cost. -/
namespace Falconer

 theorem scalar_minimal_heavy_suffix (w : ℕ → ℝ) (theta : ℝ) (N : ℕ)
    (hheavy : theta*(N:ℝ) < ∑ i ∈ Finset.range N, w i) :
    ∃ r : ℕ, 0 < r ∧ r ≤ N ∧
      theta*(r:ℝ) < ∑ i ∈ Finset.Ico (N-r) N, w i ∧
      ∀ s < r, (∑ i ∈ Finset.Ico (N-s) N, w i) ≤ theta*(s:ℝ) := by
  let P := fun r : ℕ => theta*(r:ℝ) < ∑ i ∈ Finset.Ico (N-r) N, w i
  have hex : ∃ r, P r := by
    refine ⟨N,?_⟩
    simpa only [P,Nat.sub_self,Nat.Ico_zero_eq_range] using hheavy
  let r := Nat.find hex
  have hr : P r := Nat.find_spec hex
  have hrN : r ≤ N := Nat.find_min' hex (by
    simpa only [P,Nat.sub_self,Nat.Ico_zero_eq_range] using hheavy)
  have hr0 : 0 < r := by
    by_contra h
    have hz : r = 0 := by omega
    simp only [P,hz,Nat.sub_zero,Finset.Ico_self,Finset.sum_empty,Nat.cast_zero,mul_zero,lt_self_iff_false] at hr
  refine ⟨r,hr0,hrN,hr,?_⟩
  intro s hs
  exact le_of_not_gt (Nat.find_min hex hs)

 theorem scalar_heavy_suffix_trim (w : ℕ → ℝ) (theta : ℝ) (N r t : ℕ)
    (hr : r ≤ N) (ht : t < r)
    (hheavy : theta*(r:ℝ) < ∑ i ∈ Finset.Ico (N-r) N, w i)
    (hminimal : ∀ s < r, (∑ i ∈ Finset.Ico (N-s) N, w i) ≤ theta*(s:ℝ)) :
    (∑ i ∈ Finset.Ico (N-t) N, w i) ≤ theta*(t:ℝ) ∧
      theta*((r-t:ℕ):ℝ) < ∑ i ∈ Finset.Ico (N-r) (N-t), w i := by
  have htail := hminimal t ht
  have hsum := Finset.sum_Ico_consecutive w (show N-r ≤ N-t by omega) (show N-t ≤ N by omega)
  have hcast : ((r-t:ℕ):ℝ) = (r:ℝ)-(t:ℝ) := Nat.cast_sub ht.le
  refine ⟨htail,?_⟩
  rw [hcast]
  nlinarith

 def scalarBunchTrim (r : ℕ) : ℕ := if r ≤ 1000 then 0 else r/100

 theorem scalarBunchTrim_lt {r : ℕ} (hr : 0 < r) : scalarBunchTrim r < r := by
  unfold scalarBunchTrim
  split_ifs with h
  · exact hr
  · exact Nat.div_lt_self hr (by decide)

 theorem scalarBunchTrim_budget (r : ℕ) : 100*scalarBunchTrim r ≤ r := by
  unfold scalarBunchTrim
  split_ifs
  · omega
  · have hh := Nat.div_mul_le_self r 100
    omega

 theorem scalarBunchTrim_lower {r : ℕ} (hr : 1000 < r) : r ≤ 200*scalarBunchTrim r := by
  unfold scalarBunchTrim
  rw [ite_eq_right (by omega)]
  have hmod := Nat.mod_lt r (by decide : 0 < 100)
  have hdiv := Nat.mod_add_div r 100
  omega

 theorem scalar_bunch_retained_weight (w : ℕ → ℝ) {theta : ℝ} (htheta : 0 ≤ theta)
    (N r : ℕ) (hr0 : 0 < r) (hr : r ≤ N)
    (hheavy : theta*(r:ℝ) < ∑ i ∈ Finset.Ico (N-r) N, w i)
    (hminimal : ∀ s < r, (∑ i ∈ Finset.Ico (N-s) N, w i) ≤ theta*(s:ℝ)) :
    (∑ i ∈ Finset.Ico (N-scalarBunchTrim r) N, w i) ≤ theta*(r:ℝ)/100 ∧
      (99/100:ℝ)*theta*(r:ℝ) <
        ∑ i ∈ Finset.Ico (N-r) (N-scalarBunchTrim r), w i := by
  have hh := scalar_heavy_suffix_trim w theta N r (scalarBunchTrim r) hr (scalarBunchTrim_lt hr0) hheavy hminimal
  have hb : 100*(scalarBunchTrim r:ℝ) ≤ (r:ℝ) := by exact_mod_cast scalarBunchTrim_budget r
  have hcost := mul_le_mul_of_nonneg_left hb htheta
  have hcast : ((r-scalarBunchTrim r:ℕ):ℝ) = (r:ℝ)-(scalarBunchTrim r:ℝ) :=
    Nat.cast_sub (scalarBunchTrim_lt hr0).le
  rw [hcast] at hh
  constructor <;> nlinarith

end Falconer

end OAI
