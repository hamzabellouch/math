import OAI.Probability.DilutedSpin.PoissonCountThinning

namespace OAI

namespace FixedClauseThreshold.Computability.PositiveInterpolation
open DilutedSpinGlass _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory
open scoped BigOperators

structure InterpolationAdmissible {p : ℕ} (M : Model p) : Prop where
  arity : 2 ≤ p
  density : 0 < M.alpha
  interaction_integrable : Integrable (fun z : InteractionSample p => ‖z.1‖)
    M.disorder.toMeasure
  field_integrable : Integrable (fun h : ℝ => |h|) M.field.toMeasure
  factorization : ∀ᵐ z ∂M.disorder.toMeasure,
    0 < z.2.1 ∧ ∀ s : Fin p → Spin,
      Real.exp (z.1 s) = z.2.1 * (1 + z.2.2.1 * ∏ l, z.2.2.2 l (s l)) ∧
      |z.2.2.1 * ∏ l, z.2.2.2 l (s l)| < 1
  independent_f : iIndepFun (fun l (z : InteractionSample p) => z.2.2.2 l)
    M.disorder.toMeasure
  identically_distributed_f : ∀ l j : Fin p,
    IdentDistrib (fun z : InteractionSample p => z.2.2.2 l)
      (fun z : InteractionSample p => z.2.2.2 j)
      M.disorder.toMeasure M.disorder.toMeasure
  independent_b : IndepFun (fun z : InteractionSample p => z.2.2.1)
    (fun z : InteractionSample p => z.2.2.2) M.disorder.toMeasure
  finite_b_moments : ∀ n : ℕ, 1 ≤ n →
    Integrable (fun z : InteractionSample p => (-z.2.2.1) ^ n) M.disorder.toMeasure
  positivity : ∀ n : ℕ, 1 ≤ n →
    0 ≤ ∫ z : InteractionSample p, (-z.2.2.1) ^ n ∂M.disorder.toMeasure

  raw_nonnegative : ∀ (n : ℕ), 1 ≤ n → ∀ (j : Fin p)
    (P B : FiniteLaw (Fin n → Spin)),
    0 ≤ rawReplicaMoment M (fun _ : Fin p => P) -
      (p : ℝ) * rawReplicaMoment M (fun l : Fin p => if l = j then P else B) +
      ((p - 1 : ℕ) : ℝ) * rawReplicaMoment M (fun _ : Fin p => B)

lemma rawReplica_combination_nonneg {p n : ℕ} (M : Model p)
    (hM : InterpolationAdmissible M) (hn : 1 ≤ n) (j : Fin p)
    (P B : FiniteLaw (Fin n → Spin)) :
    0 ≤ rawReplicaMoment M (fun _ : Fin p => P) -
      (p : ℝ) * rawReplicaMoment M (fun l : Fin p => if l = j then P else B) +
      ((p - 1 : ℕ) : ℝ) * rawReplicaMoment M (fun _ : Fin p => B) :=
  hM.raw_nonnegative n hn j P B

end FixedClauseThreshold.Computability.PositiveInterpolation

end OAI
