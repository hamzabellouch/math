import Mathlib.MeasureTheory.Group.Arithmetic
import OAI.Combinatorics.BalancedRyser.Profiles.Profile
import OAI.Combinatorics.BalancedRyser.Profiles.ProfileContinuity

namespace OAI

open MeasureTheory
open scoped Topology

namespace Balanced.ProfileContinuity

theorem row_sum_eq_selected_sum (p : Profile) (hp : Summable p) (i : ℕ) :
    (∑' j, p (i, j)) = ∑' ij, p ij * (if ij.1 = i then 1 else 0) := by
  classical
  have hs := summable_mul_of_abs_le_one hp
    (w := fun ij => if ij.1 = i then 1 else 0) (by intro ij; split_ifs <;> norm_num)
  rw [hs.tsum_prod]
  simp only [mul_ite, mul_one, mul_zero]
  conv_rhs =>
    arg 1
    ext k
    rw [show (∑' j, if k = i then p (k, j) else 0) =
      if k = i then ∑' j, p (k, j) else 0 by
        by_cases hk : k = i <;> simp [hk]]
  simp

theorem continuous_profile_row_sum {S : Set Profile}
    (hnonneg : ∀ p ∈ S, ∀ ij, 0 ≤ p ij)
    (hsum : ∀ p ∈ S, HasSum p 1) (i : ℕ) :
    Continuous (fun p : S => ∑' j, p.val (i, j)) := by
  classical
  have hc : Continuous (fun p : S =>
      ∑' ij, p.val ij * (if ij.1 = i then 1 else 0)) := by
    apply continuous_tsum_mul_of_probability_mass
    · exact fun p => hnonneg p.val p.property
    · exact fun p => hsum p.val p.property
    · intro ij
      exact (continuous_apply ij).comp continuous_subtype_val
    · intro ij
      exact continuous_const
    · intro p ij
      split_ifs <;> norm_num
  convert hc using 1
  funext p
  exact row_sum_eq_selected_sum p.val (hsum p.val p.property).summable i

theorem continuous_boundedProfile_row_sum (M : ℝ) (i : ℕ) :
    Continuous (fun p : {p : Profile | IsBoundedProfile M p} =>
      ∑' j : ℕ, p.val (i, j)) :=
  continuous_profile_row_sum (fun _ hp => hp.1) (fun _ hp => hp.2.1) i

theorem continuous_profile_column_sum {S : Set Profile}
    (hnonneg : ∀ p ∈ S, ∀ ij, 0 ≤ p ij)
    (hsum : ∀ p ∈ S, HasSum p 1) (j : ℕ) :
    Continuous (fun p : S => ∑' i, p.val (i, j)) := by
  classical
  have hc : Continuous (fun p : S =>
      ∑' ij, p.val ij * (if ij.2 = j then 1 else 0)) := by
    apply continuous_tsum_mul_of_probability_mass
    · exact fun p => hnonneg p.val p.property
    · exact fun p => hsum p.val p.property
    · intro ij
      exact (continuous_apply ij).comp continuous_subtype_val
    · intro ij
      exact continuous_const
    · intro p ij
      split_ifs <;> norm_num
  convert hc using 1
  funext p
  have hs := summable_mul_of_abs_le_one (hsum p.val p.property).summable
    (w := fun ij => if ij.2 = j then 1 else 0) (by intro ij; split_ifs <;> norm_num)
  rw [hs.tsum_prod]
  simp

theorem continuous_boundedProfile_column_sum (M : ℝ) (j : ℕ) :
    Continuous (fun p : {p : Profile | IsBoundedProfile M p} =>
      ∑' i : ℕ, p.val (i, j)) :=
  continuous_profile_column_sum (fun _ hp => hp.1) (fun _ hp => hp.2.1) j

theorem measurable_profile_row_sum (i : ℕ) :
    Measurable (fun p : Profile => ∑' j : ℕ, p (i, j)) :=
  Measurable.tsum (fun j => measurable_pi_apply (i, j))

theorem measurable_profile_column_sum (j : ℕ) :
    Measurable (fun p : Profile => ∑' i : ℕ, p (i, j)) :=
  Measurable.tsum (fun i => measurable_pi_apply (i, j))

end Balanced.ProfileContinuity

end OAI
