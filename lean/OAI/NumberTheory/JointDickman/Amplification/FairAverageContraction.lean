import OAI.NumberTheory.JointDickman.Analysis.FairLaplaceFeature

namespace OAI

/-! # The conditional fair-split average contracts squared error -/
namespace JointDickman
open Finset Classical

theorem finite_probability_square_le {A : Type*} [Fintype A]
    (w f : A → ℝ) (hw : ∀ a, 0 ≤ w a) (hs : ∑ a, w a = 1) :
    (∑ a, w a*f a)^2 ≤ ∑ a, w a*(f a)^2 := by
  have hh := sum_sq_le_sum_mul_sum_of_sq_le_mul (univ : Finset A)
    (f := w) (g := fun a => w a*(f a)^2) (r := fun a => w a*f a)
    (fun a _ => hw a) (fun a _ => mul_nonneg (hw a) (sq_nonneg (f a)))
    (fun a _ => by ring_nf; exact le_rfl)
  simpa only [hs,one_mul] using hh

theorem fairSplitAverage_square_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (x : ι → Bool) (f : (ι → Bool) → ℝ) :
    (fairSplitAverage x f)^2 ≤ fairSplitAverage x (fun y => (f y)^2) :=
  finite_probability_square_le (fairRetentionMass x) f
    (fairRetentionMass_nonneg x) (fairRetentionMass_sum x)

theorem fairSplitAverage_sub {ι : Type*} [Fintype ι] [DecidableEq ι]
    (x : ι → Bool) (f g : (ι → Bool) → ℝ) :
    fairSplitAverage x f-fairSplitAverage x g = fairSplitAverage x (fun y => f y-g y) := by
  simp only [fairSplitAverage,mul_sub,sum_sub_distrib]

theorem fairSplitAverage_square_error {ι : Type*} [Fintype ι] [DecidableEq ι]
    (q : ι → ℝ) (hq : ∀ i, 0 ≤ q i ∧ q i ≤ 1) (f g : (ι → Bool) → ℝ) :
    (∑ x, bernoulliSiteMass q x*(fairSplitAverage x f-fairSplitAverage x g)^2) ≤
      ∑ y, bernoulliSiteMass (fun i => q i/2) y*(f y-g y)^2 := by
  simp_rw [fairSplitAverage_sub]
  calc
    _ ≤ ∑ x, bernoulliSiteMass q x*fairSplitAverage x (fun y => (f y-g y)^2) :=
      sum_le_sum (fun x _ => mul_le_mul_of_nonneg_left
        (fairSplitAverage_square_le x _) (bernoulliSiteMass_nonneg q hq x))
    _ = _ := fairSplitAverage_marginal q _

end JointDickman

end OAI
