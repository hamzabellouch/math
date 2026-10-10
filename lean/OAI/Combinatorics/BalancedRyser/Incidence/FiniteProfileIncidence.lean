import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic

namespace OAI

open MeasureTheory
open scoped BigOperators

namespace Balanced
open scoped _root_.Balanced

theorem sum_profile_cell_incidence {Point Line : Type*}
    (S : Finset Point) (D : Finset Line) (On : Point → Line → Prop)
    [DecidableRel On] (i : ℕ)
    (hdegree : ∀ p ∈ S, (D.filter (On p)).card = i) :
    ∑ l ∈ D, (S.filter (fun p => On p l)).card = i * S.card := by
  calc
    _ = ∑ p ∈ S, (D.filter (On p)).card := by
      symm
      exact Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow On
    _ = ∑ _p ∈ S, i := Finset.sum_congr rfl hdegree
    _ = i * S.card := by simp [Nat.mul_comm]

theorem deletion_profile_cell_incidence {Point Line : Type*}
    (A : Finset Point) (D C : Finset Line) (On : Point → Line → Prop)
    [DecidableRel On] (i j : ℕ) :
    let S := A.filter (fun p => (D.filter (On p)).card = i ∧
      (C.filter (On p)).card = j)
    ∑ l ∈ D, (S.filter (fun p => On p l)).card = i * S.card := by
  dsimp only
  apply sum_profile_cell_incidence
  intro p hp
  exact (Finset.mem_filter.mp hp).2.1

theorem cover_profile_cell_incidence {Point Line : Type*}
    (A : Finset Point) (D C : Finset Line) (On : Point → Line → Prop)
    [DecidableRel On] (i j : ℕ) :
    let S := A.filter (fun p => (D.filter (On p)).card = i ∧
      (C.filter (On p)).card = j)
    ∑ l ∈ C, (S.filter (fun p => On p l)).card = j * S.card := by
  dsimp only
  apply sum_profile_cell_incidence
  intro p hp
  exact (Finset.mem_filter.mp hp).2.2

theorem normalized_profile_cell_incidence {Point Line : Type*}
    (S : Finset Point) (D : Finset Line) (On : Point → Line → Prop)
    [DecidableRel On] (i : ℕ) (q : ℝ)
    (hdegree : ∀ p ∈ S, (D.filter (On p)).card = i) :
    q⁻¹ * (∑ l ∈ D, ((S.filter (fun p => On p l)).card : ℝ) / q) =
      (i : ℝ) * ((S.card : ℝ) / q ^ 2) := by
  have hcount : (∑ l ∈ D, ((S.filter (fun p => On p l)).card : ℝ)) =
      (i : ℝ) * (S.card : ℝ) := by
    exact_mod_cast sum_profile_cell_incidence S D On i hdegree
  rw [← Finset.sum_div, hcount]
  ring

theorem integral_empirical_profile {Line Ω : Type*} [MeasurableSpace Ω]
    [MeasurableSingletonClass Ω] (D : Finset Line) (X : Line → Ω)
    (f : Ω → ℝ) (q : ℝ) (hq : 0 ≤ q) :
    (∫ ω, f ω ∂((ENNReal.ofReal q⁻¹) • ∑ l ∈ D, Measure.dirac (X l))) =
      q⁻¹ * ∑ l ∈ D, f (X l) := by
  rw [integral_smul_measure, ENNReal.toReal_ofReal (inv_nonneg.mpr hq)]
  rw [integral_finsetSum_measure (fun _ _ => integrable_dirac (by simp))]
  simp

theorem empirical_profile_mass {Line Ω : Type*} [MeasurableSpace Ω]
    [MeasurableSingletonClass Ω] (D : Finset Line) (X : Line → Ω)
    (q : ℝ) (hq : 0 ≤ q) :
    ((ENNReal.ofReal q⁻¹) • ∑ l ∈ D, Measure.dirac (X l)).real Set.univ =
      (D.card : ℝ) / q := by
  have h := integral_empirical_profile D X (fun _ => 1) q hq
  simpa [div_eq_mul_inv, mul_comm] using h

theorem integral_empirical_profile_incidence {Point Line Ω : Type*}
    [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    (S : Finset Point) (D : Finset Line) (On : Point → Line → Prop)
    [DecidableRel On] (i : ℕ) (q : ℝ) (hq : 0 ≤ q)
    (X : Line → Ω) (coord : Ω → ℝ)
    (hdegree : ∀ p ∈ S, (D.filter (On p)).card = i)
    (hcoord : ∀ l ∈ D, coord (X l) = (S.filter (fun p => On p l)).card / q) :
    (∫ ω, coord ω ∂((ENNReal.ofReal q⁻¹) • ∑ l ∈ D, Measure.dirac (X l))) =
      (i : ℝ) * ((S.card : ℝ) / q ^ 2) := by
  rw [integral_empirical_profile D X coord q hq]
  calc
    _ = q⁻¹ * ∑ l ∈ D, ((S.filter (fun p => On p l)).card : ℝ) / q := by
      congr 1
      exact Finset.sum_congr rfl hcoord
    _ = _ := normalized_profile_cell_incidence S D On i q hdegree

end Balanced

end OAI
