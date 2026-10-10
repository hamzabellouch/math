import OAI.Probability.SATComputability.PoissonKilling

namespace OAI

namespace FixedClauseThreshold.Computability

open DilutedSpinGlass MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal

theorem finiteLaw_weight_le_one {Ω : Type*} [Fintype Ω] (P : FiniteLaw Ω) (x : Ω) :
    P.weight x ≤ 1 := by
  rw [← P.total]
  exact Finset.single_le_sum (fun y _ => P.nonneg y) (Finset.mem_univ x)

theorem poisson_weight_integrable {Ω : Type*} [Fintype Ω]
    (r : ℝ≥0) (P : ℕ → FiniteLaw Ω) (x : Ω) :
    Integrable (fun m => (P m).weight x) (poissonMeasure r) := by
  apply Integrable.of_bound (measurable_of_countable _).aestronglyMeasurable 1
  exact Eventually.of_forall (fun m => abs_le.mpr
    ⟨by linarith [(P m).nonneg x], finiteLaw_weight_le_one (P m) x⟩)

noncomputable def poissonMixture {Ω : Type*} [Fintype Ω]
    (r : ℝ≥0) (P : ℕ → FiniteLaw Ω) : FiniteLaw Ω where
  weight x := ∫ m, (P m).weight x ∂poissonMeasure r
  nonneg x := integral_nonneg (fun m => (P m).nonneg x)
  total := by
    rw [← integral_finsetSum _ (fun x _ => poisson_weight_integrable r P x)]
    simp only [(P _).total, integral_const, probReal_univ, one_smul]

theorem poissonMixture_expect {Ω : Type*} [Fintype Ω]
    (r : ℝ≥0) (P : ℕ → FiniteLaw Ω) (f : Ω → ℝ) :
    (poissonMixture r P).expect f =
      ∫ m, (P m).expect f ∂poissonMeasure r := by
  simp only [FiniteLaw.expect, poissonMixture]
  rw [integral_finsetSum _ (fun x _ => (poisson_weight_integrable r P x).mul_const (f x))]
  apply Finset.sum_congr rfl
  intro x _
  rw [integral_mul_const]

theorem poissonMixture_integrable_expect {Ω : Type*} [Fintype Ω]
    (r : ℝ≥0) (P : ℕ → FiniteLaw Ω) (f : Ω → ℝ) :
    Integrable (fun m => (P m).expect f) (poissonMeasure r) := by
  unfold FiniteLaw.expect
  exact integrable_finsetSum _ (fun x _ => (poisson_weight_integrable r P x).mul_const (f x))

noncomputable def candidateFixedBlock {n : ℕ} [NeZero n]
    (k d : ℕ) (U : Finset (DeletionCandidate n)) : FiniteLaw (Finset (DeletionCandidate n)) where
  weight V := (FiniteLaw.uniform : FiniteLaw (Fin d → Fin k → SignedLiteral n)).expect
    (fun cs => if candidateResidual U cs = V then 1 else 0)
  nonneg V := FiniteLaw.expect_nonneg _ (fun _ => by split <;> norm_num)
  total := by
    classical
    rw [← FiniteLaw.expect_fintype_sum]
    simp

theorem candidateFixedBlock_expect {n : ℕ} [NeZero n]
    (k d : ℕ) (U : Finset (DeletionCandidate n))
    (f : Finset (DeletionCandidate n) → ℝ) :
    (candidateFixedBlock k d U).expect f = (candidateStep k)^[d] f U := by
  classical
  rw [candidateStep_iterate]
  change (∑ V, FiniteLaw.expect _ _ * f V) = _
  simp_rw [← FiniteLaw.expect_mul_right]
  rw [← FiniteLaw.expect_fintype_sum]
  apply FiniteLaw.expect_congr
  intro cs
  simp

noncomputable def candidateBlock {n : ℕ} [NeZero n]
    (r : ℝ≥0) (k : ℕ) (U : Finset (DeletionCandidate n)) :
    FiniteLaw (Finset (DeletionCandidate n)) :=
  poissonMixture r (fun d => candidateFixedBlock k d U)

theorem candidateBlock_expect {n : ℕ} [NeZero n]
    (r : ℝ≥0) (k : ℕ) (U : Finset (DeletionCandidate n))
    (f : Finset (DeletionCandidate n) → ℝ) :
    (candidateBlock r k U).expect f =
      ∫ d, (candidateStep k)^[d] f U ∂poissonMeasure r := by
  rw [candidateBlock, poissonMixture_expect]
  simp only [candidateFixedBlock_expect]

theorem candidateBlock_kill {n : ℕ} [NeZero n]
    (r : ℝ≥0) (k : ℕ) (U : Finset (DeletionCandidate n)) :
    (candidateBlock r k U).expect (fun V => if V = ∅ then 1 else 0) =
      poissonKillProbability U k r := by
  classical
  rw [candidateBlock, poissonMixture_expect]
  unfold poissonKillProbability
  congr 1
  funext d
  rw [candidateFixedBlock_expect, candidateStep_iterate]
  unfold batchKillProbability
  apply FiniteLaw.expect_congr
  intro cs
  exact if_congr (candidateResidual_empty_iff U cs) rfl rfl

end FixedClauseThreshold.Computability

end OAI
