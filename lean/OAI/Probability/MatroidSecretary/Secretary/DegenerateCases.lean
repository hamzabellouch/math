import OAI.Probability.MatroidSecretary.Weights.ZeroBenchmark
import OAI.Probability.MatroidSecretary.Secretary.Execution

namespace OAI

/-!
# Exceptional inputs for the actual secretary execution

These lemmas specialize the canonical history-only secretary model. They do not
assume a conditional-mask coupling and do not replace the competitive theorem.
All pointwise statements hold for every complete initial seed, including seeds
outside the support of a chosen probability law.
-/

namespace MatroidProphet.ZeroBenchmark

open MeasureTheory

/-- A feasible secretary rule has zero realized reward whenever actual OPT is zero. -/
theorem secretaryReward_eq_zero {n : ℕ} {Q : Type*} [MeasurableSpace Q]
    (M : Matroid (Fin n)) (A : SecretaryRule n Q) (hA : SecretaryFeasible M A)
    (q : Q) (w : Weights n) (hw : ∀ e, 0 ≤ w e) (π : ArrivalOrder n)
    (hopt : optimum M w = 0) : secretaryReward A q w π = 0 := by
  apply le_antisymm
  · exact (secretaryReward_le_optimum M A hA q w hw π).trans_eq hopt
  · exact secretaryReward_nonneg A q w π hw

/-- There is no moment or independence condition in the zero-benchmark case. -/
theorem integrable_secretaryReward_of_optimum_zero {n : ℕ} {Q Ω : Type*}
    [MeasurableSpace Q] [MeasurableSpace Ω]
    (M : Matroid (Fin n)) (A : SecretaryRule n Q) (hA : SecretaryFeasible M A)
    (w : Weights n) (hw : ∀ e, 0 ≤ w e) (hopt : optimum M w = 0)
    (μ : Measure Ω) (q : Ω → Q) (π : Ω → ArrivalOrder n) :
    Integrable (fun ω => secretaryReward A (q ω) w (π ω)) μ := by
  apply (integrable_zero Ω ℝ μ).congr
  exact ae_of_all μ fun ω => (secretaryReward_eq_zero M A hA (q ω) w hw (π ω) hopt).symm

/-- Even an arbitrary full-seed-aware order has zero expected reward at zero OPT. -/
theorem integral_secretaryReward_of_optimum_zero {n : ℕ} {Q Ω : Type*}
    [MeasurableSpace Q] [MeasurableSpace Ω]
    (M : Matroid (Fin n)) (A : SecretaryRule n Q) (hA : SecretaryFeasible M A)
    (w : Weights n) (hw : ∀ e, 0 ≤ w e) (hopt : optimum M w = 0)
    (μ : Measure Ω) (q : Ω → Q) (π : Ω → ArrivalOrder n) :
    (∫ ω, secretaryReward A (q ω) w (π ω) ∂μ) = 0 := by
  simp only [secretaryReward_eq_zero M A hA _ w hw _ hopt]
  exact integral_zero _ _

/-- A fully sacrificed instance never accepts, even after the last arrival. -/
theorem secretaryAcceptedThrough_eq_empty_of_full_prefix {n : ℕ} {Q : Type*}
    [MeasurableSpace Q] (A : SecretaryRule n Q) (q : Q)
    (hfull : (A.prefixLength q).val = n) (w : Weights n)
    (π : ArrivalOrder n) (t : ℕ) : secretaryAcceptedThrough A q w π t = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro e he
  have hle := secretaryAcceptedThrough_not_prefix A q w π t e he
  rw [hfull] at hle
  exact (not_le_of_gt (π.symm e).isLt) hle

/-- Full-prefix sacrifice forces zero reward without feasibility or sign assumptions. -/
theorem secretaryReward_eq_zero_of_full_prefix {n : ℕ} {Q : Type*}
    [MeasurableSpace Q] (A : SecretaryRule n Q) (q : Q)
    (hfull : (A.prefixLength q).val = n) (w : Weights n)
    (π : ArrivalOrder n) : secretaryReward A q w π = 0 := by
  simp [secretaryReward, secretaryAcceptedThrough_eq_empty_of_full_prefix A q hfull]

/-- Empty-ground execution is defined and empty for every seed and time. -/
theorem secretaryAcceptedThrough_empty {Q : Type*} [MeasurableSpace Q]
    (A : SecretaryRule 0 Q) (q : Q) (w : Weights 0)
    (π : ArrivalOrder 0) (t : ℕ) : secretaryAcceptedThrough A q w π t = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro e
  exact Fin.elim0 e

/-- Empty-ground reward is identically zero, with no positive-size premise. -/
theorem secretaryReward_empty {Q : Type*} [MeasurableSpace Q]
    (A : SecretaryRule 0 Q) (q : Q) (w : Weights 0)
    (π : ArrivalOrder 0) : secretaryReward A q w π = 0 := by
  simp [secretaryReward, secretaryAcceptedThrough_empty]

end MatroidProphet.ZeroBenchmark

end OAI
