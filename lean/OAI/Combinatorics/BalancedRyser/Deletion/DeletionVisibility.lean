import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic
import OAI.Combinatorics.BalancedRyser.Profiles.Profile
import OAI.Combinatorics.BalancedRyser.Profiles.ProfilePoissonLemmas

namespace OAI

namespace Balanced
open scoped _root_.Balanced

open MeasureTheory
open scoped NNReal

theorem deletionVisible_positive_of_not_poisson
    (k : ℕ) (P : Profile) (ν : Measure Profile) [IsFiniteMeasure ν]
    (hmass : ν.real Set.univ = (k : ℝ))
    (hnormalized : HasSum (fun i : ℕ => P (i, 0)) 1)
    (hincidence : ∀ i : ℕ,
      (∫ x : Profile, x (i + 1, 0) ∂ν) = (i + 1 : ℝ) * P (i + 1, 0))
    (hnot : (fun i : ℕ => P (i, 0)) ≠ deletionPoissonMass k) :
    0 < ν.real (deletionVisible P) := by
  by_contra hpositive
  have hzero : ν.real (deletionVisible P) = 0 :=
    le_antisymm (le_of_not_gt hpositive) measureReal_nonneg
  have hinvisible : ∀ᵐ x : Profile ∂ν, deletionInvisible P x := by
    apply ae_iff.mpr
    exact (measureReal_eq_zero_iff).mp hzero
  have hrec : ∀ i : ℕ, (i + 1 : ℝ) * P (i + 1, 0) = (k : ℝ) * P (i, 0) := by
    intro i
    calc
      (i + 1 : ℝ) * P (i + 1, 0) = ∫ x : Profile, x (i + 1, 0) ∂ν :=
        (hincidence i).symm
      _ = ∫ _x : Profile, P (i, 0) ∂ν := by
        apply integral_congr_ae
        filter_upwards [hinvisible] with x hx
        simpa [deletionInvisible] using hx (i + 1) 0
      _ = (k : ℝ) * P (i, 0) := by
        rw [integral_const, hmass]
        rfl
  apply hnot
  funext i
  unfold deletionPoissonMass
  simpa only [NNReal.coe_natCast] using
    profile_recurrence_eq_poissonMeasure (p := fun n => P (n, 0)) (k : ℝ≥0)
      hnormalized hrec i

theorem deletionVisible_positive_of_tv
    (k : ℕ) (P : Profile) (ν : Measure Profile) [IsFiniteMeasure ν]
    (hmass : ν.real Set.univ = (k : ℝ))
    (hnormalized : HasSum (fun i : ℕ => P (i, 0)) 1)
    (hincidence : ∀ i : ℕ,
      (∫ x : Profile, x (i + 1, 0) ∂ν) = (i + 1 : ℝ) * P (i + 1, 0))
    (htv : 0 < (1 / 2 : ℝ) * ∑' i : ℕ, |P (i, 0) - deletionPoissonMass k i|) :
    0 < ν.real (deletionVisible P) := by
  apply deletionVisible_positive_of_not_poisson k P ν hmass hnormalized hincidence
  intro heq
  have hpoint (i : ℕ) : P (i, 0) = deletionPoissonMass k i := congrFun heq i
  simp only [hpoint, sub_self, abs_zero, tsum_zero, mul_zero] at htv
  exact (lt_irrefl 0) htv

end Balanced

end OAI
