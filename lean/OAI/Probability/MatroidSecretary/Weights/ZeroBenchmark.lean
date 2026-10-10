import OAI.Probability.MatroidProphet.Main
import Mathlib.MeasureTheory.Integral.Bochner.Basic

namespace OAI

namespace MatroidProphet.ZeroBenchmark

open MeasureTheory Finset
open scoped Classical

/-- Only singleton-independent labels can affect the offline optimum.
No sign or integrability assumption is necessary for this identity. -/
theorem optimum_congr_on_singletons {n : ℕ} (M : Matroid (Fin n))
    (w v : Weights n)
    (h : ∀ e, M.Indep ({e} : Set (Fin n)) → w e = v e) :
    optimum M w = optimum M v := by
  classical
  unfold optimum
  apply Finset.sup'_congr Finset.univ_nonempty rfl
  intro I _
  by_cases hI : M.Indep (I : Set (Fin n))
  · simp only [ite_eq_left hI]
    apply Finset.sum_congr rfl
    intro e he
    exact h e (hI.subset (Set.singleton_subset_iff.mpr he))
  · simp only [ite_eq_right hI]

/-- The zero-weight benchmark is zero, also for empty or rank-zero matroids. -/
@[simp] theorem optimum_zero {n : ℕ} (M : Matroid (Fin n)) :
    optimum M (fun _ => 0) = 0 := by
  classical
  simp [optimum]

/-- On nonnegative inputs, a zero benchmark is exactly the condition that
every label that could be accepted on its own has zero weight. -/
theorem optimum_eq_zero_iff {n : ℕ} (M : Matroid (Fin n))
    (w : Weights n) (hw : ∀ e, 0 ≤ w e) :
    optimum M w = 0 ↔ ∀ e, M.Indep ({e} : Set (Fin n)) → w e = 0 := by
  constructor
  · intro h e he
    have hb := sum_le_optimum M w {e} (by simpa using he)
    simp only [Finset.sum_singleton, h] at hb
    exact le_antisymm hb (hw e)
  · intro h
    rw [optimum_congr_on_singletons M w (fun _ => 0) h]
    exact optimum_zero M

/-- Replacing all loop coordinates by zero never changes the objective.
Here ground-set outsiders, if any, are also harmless. -/
theorem optimum_ignore_infeasible_coordinates {n : ℕ} (M : Matroid (Fin n))
    (w : Weights n) :
    optimum M (fun e => if M.Indep ({e} : Set (Fin n)) then w e else 0) =
      optimum M w := by
  classical
  apply optimum_congr_on_singletons
  intro e he
  simp only [ite_eq_left he]

/-- Rank-zero behavior needs no bound at all on the values of its labels. -/
theorem optimum_eq_zero_of_no_independent_singleton {n : ℕ}
    (M : Matroid (Fin n))
    (hM : ∀ e, ¬ M.Indep ({e} : Set (Fin n))) (w : Weights n) :
    optimum M w = 0 := by
  rw [optimum_congr_on_singletons M w (fun _ => 0) (fun e he => (hM e he).elim)]
  exact optimum_zero M

/-- The empty instance has the zero benchmark without a positive-size premise. -/
@[simp] theorem optimum_empty (M : Matroid (Fin 0)) (w : Weights 0) :
    optimum M w = 0 := by
  apply optimum_eq_zero_of_no_independent_singleton
  intro e
  exact Fin.elim0 e

/-- Every feasible realized hidden reward vanishes when the benchmark does. -/
theorem hiddenReward_eq_zero {n bits : ℕ} (M : Matroid (Fin n))
    (A : HiddenRule n bits) (r : Seed bits) (w : Weights n)
    (π : ArrivalOrder n) (hw : ∀ e, 0 ≤ w e)
    (hA : M.Indep (hiddenAcceptedThrough A r w π n : Set (Fin n)))
    (hopt : optimum M w = 0) : hiddenReward A r w π = 0 := by
  apply le_antisymm
  · exact (sum_le_optimum M w _ hA).trans_eq hopt
  · exact Finset.sum_nonneg fun e _ => hw e

/-- The zero-benchmark conclusion also holds for the minimum taken separately
at each complete seed, before any expectation. -/
theorem hiddenWorstReward_eq_zero {n bits : ℕ} (M : Matroid (Fin n))
    (A : HiddenRule n bits) (w : Weights n) (hw : ∀ e, 0 ≤ w e)
    (hA : ∀ r π, M.Indep (hiddenAcceptedThrough A r w π n : Set (Fin n)))
    (hopt : optimum M w = 0) (r : Seed bits) :
    hiddenWorstReward A w r = 0 := by
  apply le_antisymm
  · exact (hiddenWorstReward_le A w r (Equiv.refl _)).trans_eq
      (hiddenReward_eq_zero M A r w (Equiv.refl _) hw (hA r _) hopt)
  · exact hiddenWorstReward_nonneg A w hw r

/-- No probability-law or moment premise is needed in the zero case. -/
theorem integral_hiddenWorstReward_eq_zero {n bits : ℕ} (M : Matroid (Fin n))
    (A : HiddenRule n bits) (w : Weights n) (hw : ∀ e, 0 ≤ w e)
    (hA : ∀ r π, M.Indep (hiddenAcceptedThrough A r w π n : Set (Fin n)))
    (hopt : optimum M w = 0) (ν : Measure (Seed bits)) :
    (∫ r, hiddenWorstReward A w r ∂ν) = 0 := by
  simp only [hiddenWorstReward_eq_zero M A w hw hA hopt]
  exact integral_zero _ _

/-- Even completely unrestricted loop coordinates cannot create a moment
requirement when the usable coordinates vanish almost everywhere. -/
theorem integrable_optimum_of_usable_coordinates_zero {n : ℕ}
    (M : Matroid (Fin n)) {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (V : Ω → Weights n)
    (hV : ∀ᵐ ω ∂μ, ∀ e, M.Indep ({e} : Set (Fin n)) → V ω e = 0) :
    Integrable (fun ω => optimum M (V ω)) μ := by
  apply (integrable_zero Ω ℝ μ).congr
  filter_upwards [hV] with ω hω
  symm
  rw [optimum_congr_on_singletons M (V ω) (fun _ => 0) hω]
  exact optimum_zero M

 
theorem integral_optimum_of_usable_coordinates_zero {n : ℕ}
    (M : Matroid (Fin n)) {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (V : Ω → Weights n)
    (hV : ∀ᵐ ω ∂μ, ∀ e, M.Indep ({e} : Set (Fin n)) → V ω e = 0) :
    (∫ ω, optimum M (V ω) ∂μ) = 0 := by
  calc
    (∫ ω, optimum M (V ω) ∂μ) = ∫ _ : Ω, (0 : ℝ) ∂μ := by
      apply integral_congr_ae
      filter_upwards [hV] with ω hω
      rw [optimum_congr_on_singletons M (V ω) (fun _ => 0) hω]
      exact optimum_zero M
    _ = 0 := integral_zero _ _

end MatroidProphet.ZeroBenchmark

end OAI
