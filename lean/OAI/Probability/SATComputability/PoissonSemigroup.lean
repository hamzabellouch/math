import OAI.Probability.SATComputability.PoissonKernel

namespace OAI

namespace FixedClauseThreshold.Computability

open DilutedSpinGlass MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal

theorem finite_expect_integral {Ω X : Type*} [Fintype Ω] [MeasurableSpace X]
    (P : FiniteLaw Ω) (μ : Measure X) (f : X → Ω → ℝ)
    (hf : ∀ x, Integrable (fun m => f m x) μ) :
    P.expect (fun x => ∫ m, f m x ∂μ) = ∫ m, P.expect (f m) ∂μ := by
  unfold FiniteLaw.expect
  rw [integral_finsetSum _ (fun x _ => (hf x).const_mul (P.weight x))]
  apply Finset.sum_congr rfl
  intro x _
  rw [integral_const_mul]

theorem candidateStep_iterate_bound {n : ℕ} [NeZero n]
    (k d : ℕ) (f : Finset (DeletionCandidate n) → ℝ) {B : ℝ}
    (hf : ∀ U, |f U| ≤ B) (U : Finset (DeletionCandidate n)) :
    |(candidateStep k)^[d] f U| ≤ B := by
  rw [← candidateFixedBlock_expect]
  exact FiniteLaw.abs_expect_le _ hf

theorem candidateBlock_comp {n : ℕ} [NeZero n]
    (r s : ℝ≥0) (k : ℕ) (U : Finset (DeletionCandidate n))
    (f : Finset (DeletionCandidate n) → ℝ) :
    (candidateBlock (r+s) k U).expect f =
      (candidateBlock r k U).expect (fun V => (candidateBlock s k V).expect f) := by
  let B := ∑ V : Finset (DeletionCandidate n), |f V|
  have hf : ∀ V, |f V| ≤ B := fun V =>
    Finset.single_le_sum (fun W _ => abs_nonneg (f W)) (Finset.mem_univ V)
  have hi (v : ℝ≥0) (V : Finset (DeletionCandidate n)) :
      Integrable (fun d => (candidateStep k)^[d] f V) (poissonMeasure v) := by
    apply Integrable.of_bound (measurable_of_countable _).aestronglyMeasurable B
    exact Eventually.of_forall (fun d => by
      simpa only [Real.norm_eq_abs] using candidateStep_iterate_bound k d f hf V)
  symm
  calc
    _ = (candidateBlock r k U).expect
        (fun V => ∫ e, (candidateStep k)^[e] f V ∂poissonMeasure s) := by
      simp only [candidateBlock_expect]
    _ = ∫ e, (candidateBlock r k U).expect
        (fun V => (candidateStep k)^[e] f V) ∂poissonMeasure s :=
      finite_expect_integral _ _ _ (hi s)
    _ = ∫ e, ∫ d, (candidateStep k)^[d] ((candidateStep k)^[e] f) U
        ∂poissonMeasure r ∂poissonMeasure s := by simp only [candidateBlock_expect]
    _ = ∫ e, ∫ d, (candidateStep k)^[e+d] f U
        ∂poissonMeasure r ∂poissonMeasure s := by
      apply integral_congr_ae
      exact Eventually.of_forall (fun e => integral_congr_ae
        (Eventually.of_forall (fun d => by
          dsimp only
          rw [Nat.add_comm e d, Function.iterate_add_apply])))
    _ = ∫ m, (candidateStep k)^[m] f U ∂poissonMeasure (r+s) := by
      rw [add_comm r s, ← poissonMeasure_conv_poissonMeasure,
        integral_conv (by simpa only [poissonMeasure_conv_poissonMeasure] using hi (s+r) U)]
    _ = _ := (candidateBlock_expect _ _ _ _).symm

noncomputable def poissonCandidateStep {n : ℕ} [NeZero n] (r : ℝ≥0) (k : ℕ)
    (f : Finset (DeletionCandidate n) → ℝ) (U : Finset (DeletionCandidate n)) : ℝ :=
  (candidateBlock r k U).expect f

theorem poissonCandidateStep_iterate {n : ℕ} [NeZero n]
    (r : ℝ≥0) (k m : ℕ) (U : Finset (DeletionCandidate n))
    (f : Finset (DeletionCandidate n) → ℝ) :
    (poissonCandidateStep r k)^[m] f U = (candidateBlock (r*m) k U).expect f := by
  induction m generalizing U f with
  | zero =>
    rw [Function.iterate_zero_apply, Nat.cast_zero, mul_zero, candidateBlock_expect]
    rw [integral_poissonMeasure]
    simp [zero_pow_eq, ite_div, ite_mul]
  | succ m ih =>
    rw [Function.iterate_succ_apply']
    change (candidateBlock r k U).expect ((poissonCandidateStep r k)^[m] f) = _
    have he : (poissonCandidateStep r k)^[m] f =
        fun V => (candidateBlock (r*m) k V).expect f := funext (fun V => ih V f)
    rw [he, ← candidateBlock_comp]
    congr 2
    push_cast
    ring

end FixedClauseThreshold.Computability

end OAI
