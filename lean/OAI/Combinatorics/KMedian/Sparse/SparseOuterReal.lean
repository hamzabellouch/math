import Mathlib
import OAI.Combinatorics.KMedian.Preparation.PreparationMoments
import OAI.Combinatorics.KMedian.Sparse.SparseRealLaw
import OAI.Combinatorics.KMedian.Sparse.SparseOuterCounts

namespace OAI


                                       
section
namespace MetricKMedian.SparseOuterLaw
open Finset
open RationalWeightedStep (point)
open SparseGridRounding (base fraction)
open SparseSignedPreparation (State)
variable {n m : ℕ}

theorem outsideCount_le_at (D : Fin m → Finset (Fin n)) (c q : Fin m → ℚ)
    (hc : ∀ e, 0 ≤ c e ∧ c e ≤ 1) (hq : ∀ e, 0 ≤ q e) (L : ℕ)
    (a : Fin (law D c q hc hq).length) (e : Fin m) (hL : q e ≤ L) :
    outsideCount q (law D c q hc hq).states[a.val] e ≤ L := by
  have hb : base q e ≤ L := by exact_mod_cast (Nat.floor_le (hq e)).trans hL
  by_cases hi : 0 < point (law D c q hc hq).states[a.val].1 e
  · have hl : base q e < L := by
      by_contra hn
      have heq : base q e = L := le_antisymm hb (le_of_not_gt hn)
      have hz : point (fraction q) e = 0 := by
        simp only [fraction, point, Vector.getElem_ofFn]
        have hh := Nat.floor_le (hq e)
        change (base q e : ℚ) ≤ q e at hh
        rw [heq] at hh ⊢
        linarith only [hh, hL]
      have hf := point_fixed D c q hc hq e hz a
      rw [hf] at hi
      exact (lt_irrefl 0) hi
    simpa only [outsideCount, ite_eq_left hi] using Nat.add_one_le_iff.mpr hl
  · simpa only [outsideCount, ite_eq_right hi, Nat.add_zero] using hb

noncomputable def nominalMass (q : Fin m → ℚ) (g : ℝ) (z : State n m) (e : Fin m) : ℝ :=
  g * (SparseSignedPreparation.nominalCount (base q) z e : ℝ)

theorem nominalMass_nonneg (q : Fin m → ℚ) {g : ℝ} (hg : 0 ≤ g)
    (z : State n m) (e : Fin m) : 0 ≤ nominalMass q g z e := by
  apply mul_nonneg hg
  dsimp only [SparseSignedPreparation.nominalCount, SparseBernoulli.flag]
  split_ifs <;> positivity

theorem nominalMass_cap (D : Fin m → Finset (Fin n)) (c q : Fin m → ℚ)
    (hc : ∀ e, 0 ≤ c e ∧ c e ≤ 1) (hq : ∀ e, 0 ≤ q e) {g : ℝ} (hg : 0 ≤ g)
    (a : Fin (law D c q hc hq).length) (e : Fin m) :
    nominalMass q g (law D c q hc hq).states[a.val] e ≤
      g * (outsideCount q (law D c q hc hq).states[a.val] e : ℝ) := by
  apply mul_le_mul_of_nonneg_left _ hg
  have h := (budget D c q hc hq a).2.2.2.1 e
  rw [← outsideCount_cast] at h
  exact_mod_cast h

theorem nominalMass_mean (D : Fin m → Finset (Fin n)) (c q : Fin m → ℚ)
    (hc : ∀ e, 0 ≤ c e ∧ c e ≤ 1) (hq : ∀ e, 0 ≤ q e) (g : ℝ) (e : Fin m) :
    (law D c q hc hq).realIndex.expect
      (fun a => nominalMass q g (law D c q hc hq).states[a.val] e) = g * (q e : ℝ) := by
  simp only [nominalMass, FiniteLaw.expect_mul]
  rw [SparseIntegerLaw.realIndex_expect _ (fun z => SparseSignedPreparation.nominalCount (base q) z e), nominal_mean]

theorem nominalMass_variance (D : Fin m → Finset (Fin n)) (c q : Fin m → ℚ)
    (hc : ∀ e, 0 ≤ c e ∧ c e ≤ 1) (hq : ∀ e, 0 ≤ q e) (g : ℝ) (e : Fin m) :
    (law D c q hc hq).realIndex.variance
      (fun a => nominalMass q g (law D c q hc hq).states[a.val] e) ≤ g * (g * (q e : ℝ)) := by
  have hv : (law D c q hc hq).realIndex.variance
      (fun a => (SparseSignedPreparation.nominalCount (base q) (law D c q hc hq).states[a.val] e : ℝ)) ≤
      (q e : ℝ) := by
    apply FiniteLaw.adjacent_variance _ _ (m := (base q e : ℝ)) (Nat.cast_nonneg _) ?_ ?_
    · intro a _
      rcases (budget D c q hc hq a).2.2.1 e with h | h
      · exact Or.inl (by exact_mod_cast h)
      · exact Or.inr (by exact_mod_cast h)
    · rw [SparseIntegerLaw.realIndex_expect _ (fun z => SparseSignedPreparation.nominalCount (base q) z e), nominal_mean]
  simp only [nominalMass, FiniteLaw.variance_mul]
  simpa only [pow_two, mul_assoc] using mul_le_mul_of_nonneg_left hv (sq_nonneg g)

theorem nominalMass_pair (D : Fin m → Finset (Fin n)) (c q : Fin m → ℚ)
    (hc : ∀ e, 0 ≤ c e ∧ c e ≤ 1) (hq : ∀ e, 0 ≤ q e) (g : ℝ)
    (e f : Fin m) (hef : e ≠ f) :
    (law D c q hc hq).realIndex.expect (fun a =>
      nominalMass q g (law D c q hc hq).states[a.val] e *
      nominalMass q g (law D c q hc hq).states[a.val] f) ≤
      (g * (q e : ℝ)) * (g * (q f : ℝ)) := by
  have he := (law D c q hc hq).realIndex_expect (fun z =>
    SparseSignedPreparation.nominalCount (base q) z e *
    SparseSignedPreparation.nominalCount (base q) z f)
  simp only [Rat.cast_mul] at he
  have hh : (law D c q hc hq).realIndex.expect (fun a =>
      (SparseSignedPreparation.nominalCount (base q) (law D c q hc hq).states[a.val] e : ℝ) *
      (SparseSignedPreparation.nominalCount (base q) (law D c q hc hq).states[a.val] f : ℝ)) ≤
      (q e : ℝ) * (q f : ℝ) := by
    rw [he, ← Rat.cast_mul]
    exact Rat.cast_le.mpr (nominal_pair D c q hc hq e f hef)
  have hf : ∀ x y : ℝ, (g*x)*(g*y) = g^2*(x*y) := by intros; ring
  simpa only [nominalMass, hf, FiniteLaw.expect_mul] using
    mul_le_mul_of_nonneg_left hh (sq_nonneg g)

end MetricKMedian.SparseOuterLaw
end

end OAI
