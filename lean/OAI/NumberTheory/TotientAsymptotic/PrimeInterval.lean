import OAI.NumberTheory.TotientAsymptotic.WeightedPrimeWindow

namespace OAI

noncomputable section
open scoped Topology Classical
open Filter
namespace TotientAsymptotic

def primeInterval (l u : ℝ) : Finset ℕ :=
  (Nat.primesLE ⌊u⌋₊).filter (fun p : ℕ => l < p)

lemma primeInterval_card {l u : ℝ} (hl : 0 ≤ l) (hu : 0 ≤ u) :
    ((primeInterval l u).card : ℝ) =
      (Nat.primeCounting ⌊u⌋₊ : ℝ)-Nat.primeCounting ⌊min l u⌋₊ := by
  have he : (Nat.primesLE ⌊u⌋₊).filter (fun p : ℕ => ¬l < p)=Nat.primesLE ⌊min l u⌋₊ := by
    ext p
    simp only [Finset.mem_filter,Nat.mem_primesLE,not_lt,
      Nat.le_floor_iff hu,Nat.le_floor_iff (le_min hl hu),le_min_iff]
    tauto
  have hc := Finset.card_filter_add_card_filter_not (s := Nat.primesLE ⌊u⌋₊) (fun p : ℕ => l < p)
  rw [he,Nat.primesLE_card_eq_primeCounting] at hc
  have hc' := congrArg (fun n : ℕ => (n : ℝ)) hc
  simp only [Nat.cast_add,Nat.primesLE_card_eq_primeCounting] at hc'
  change ((primeInterval l u).card : ℝ)+_=_ at hc'
  linarith

/-- Counts may vanish: the positive part is encoded by min(l,u), so no
relative estimate for a short or empty prime interval is assumed. -/
lemma prime_interval_uniform (hpnt : PrimeNumberTheoremInput)
    {a b ε : ℝ} (ha : 0 < a) (hb : 0 < b) (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop, ∀ D l u : ℝ, 1 ≤ D →
      Real.log D ≤ (Real.log x)^(4/5 : ℝ) →
      a*x/D ≤ l → a*x/D ≤ u → u ≤ b*x/D →
      |((primeInterval l u).card : ℝ)-(u-min l u)/Real.log x| ≤
        ε*x/(D*Real.log x) := by
  filter_upwards [linear_prime_window hpnt ha hb (show 0 < ε/2 by positivity),
    eventually_gt_atTop (1 : ℝ)] with x hx hx1
  intro D l u hD hlog hl hu huo
  have hx0 : 0 < x := zero_lt_one.trans hx1
  have hD0 : 0 < D := zero_lt_one.trans_le hD
  have hl0 : 0 ≤ l := ((div_pos (mul_pos ha hx0) hD0).trans_le hl).le
  have hu0 : 0 ≤ u := ((div_pos (mul_pos ha hx0) hD0).trans_le hu).le
  have h₁ := hx D u hD hlog hu huo
  have h₂ := hx D (min l u) hD hlog (le_min hl hu) ((min_le_right _ _).trans huo)
  rw [primeInterval_card hl0 hu0]
  calc
    _ = |((Nat.primeCounting ⌊u⌋₊ : ℝ)-u/Real.log x)-
        ((Nat.primeCounting ⌊min l u⌋₊ : ℝ)-min l u/Real.log x)| := by congr 1; ring
    _ ≤ |(Nat.primeCounting ⌊u⌋₊ : ℝ)-u/Real.log x|+
        |(Nat.primeCounting ⌊min l u⌋₊ : ℝ)-min l u/Real.log x| := abs_sub _ _
    _ ≤ _ := (add_le_add h₁ h₂).trans_eq (by ring)

end TotientAsymptotic

end

end OAI
