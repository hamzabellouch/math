import OAI.Analysis.CircleDomains.Probability.DyadicMeasurePartition

namespace OAI

/-! Atomless time measures split exactly over a monotone image of a dyadic
partition. This bounds restricted physical length by the old time measure. -/

open Set MeasureTheory
open scoped ENNReal

noncomputable section

namespace CircleDomainRigidity

theorem sum_monotone_dyadic_restrict (μ : Measure PathTime) [NullSingletonClass μ]
    (f : PathTime → PathTime) (hf : Monotone f) (n : ℕ) :
    ∑ i : Fin (2 ^ n), μ.restrict (Icc (f (dyadicLeft n i)) (f (dyadicRight n i))) =
      μ.restrict (Icc (f ⊥) (f ⊤)) := by
  induction n with
  | zero =>
    change (∑ i : Fin 1, μ.restrict (Icc (f (dyadicLeft 0 i)) (f (dyadicRight 0 i)))) = _
    rw [Fin.sum_univ_one]
    have hl : dyadicLeft 0 0 = ⊥ := (dyadicNode_left 0 0).symm.trans (dyadicNode_zero 0)
    have hr : dyadicRight 0 0 = ⊤ := (dyadicNode_right 0 0).symm.trans (dyadicNode_last 0)
    rw [hl, hr]
  | succ n ih =>
    rw [sum_dyadic_children]
    convert ih using 1
    apply Finset.sum_congr rfl
    intro i _
    rw [← dyadicRight_even, ← restrict_Icc_add μ (hf (dyadicLeft_le_right _ _))]
    · rw [dyadicLeft_even, dyadicRight_odd]
    · rw [dyadicRight_even]
      exact hf (dyadicLeft_le_right _ _)

theorem sum_monotone_dyadic_mass (μ : Measure PathTime) [NullSingletonClass μ]
    (f : PathTime → PathTime) (hf : Monotone f) (n : ℕ) :
    ∑ i : Fin (2 ^ n), μ (Icc (f (dyadicLeft n i)) (f (dyadicRight n i))) =
      μ (Icc (f ⊥) (f ⊤)) := by
  have h := congrArg (fun ν : Measure PathTime => ν univ) (sum_monotone_dyadic_restrict μ f hf n)
  simpa only [Measure.coe_finsetSum, Finset.sum_apply, Measure.restrict_apply_univ] using h

end CircleDomainRigidity

end

end OAI
