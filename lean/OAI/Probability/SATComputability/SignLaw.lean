import OAI.Probability.SATComputability.SATModel
import OAI.Probability.DilutedSpin.PoissonVariance

namespace OAI

namespace FixedClauseThreshold.Computability

open DilutedSpinGlass MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal

theorem signLaw_eq_pi :
    signLaw.toMeasure = Measure.pi (fun _ : Fin 3 =>
      (PMF.uniformOfFintype Bool).toMeasure) := by
  classical
  apply Measure.ext_of_singleton
  intro J
  norm_num [signLaw, Measure.pi_singleton, PMF.uniformOfFintype_apply, ← ENNReal.inv_pow]

theorem uniformFiniteLaw_pi {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : ι → Type*} [∀ i, Fintype (A i)] [∀ i, Nonempty (A i)] :
    (FiniteLaw.uniform : FiniteLaw (∀ i, A i)) =
      FiniteLaw.pi (fun i => (FiniteLaw.uniform : FiniteLaw (A i))) := by
  apply FiniteLaw.weights_ext
  intro x
  simp [FiniteLaw.uniform, FiniteLaw.pi, Fintype.card_pi, Nat.cast_prod,
    Finset.prod_inv_distrib]

theorem signLaw_integral (f : (Fin 3 → Bool) → ℝ) :
    (∫ J, f J ∂signLaw.toMeasure) = (FiniteLaw.uniform : FiniteLaw (Fin 3 → Bool)).expect f := by
  change (∫ J, f J ∂(PMF.uniformOfFintype (Fin 3 → Bool)).toMeasure) = _
  rw [PMF.integral_eq_sum]
  simp [FiniteLaw.expect, FiniteLaw.uniform]

theorem signLaw_product (f : Fin 3 → Bool → ℝ) :
    (∫ J, (∏ l, f l (J l)) ∂signLaw.toMeasure) =
      ∏ l, (FiniteLaw.uniform : FiniteLaw Bool).expect (f l) := by
  rw [signLaw_integral, uniformFiniteLaw_pi, FiniteLaw.expect_pi_product]

theorem signLaw_independent :
    iIndepFun (fun l (J : Fin 3 → Bool) => literalFactor (J l)) signLaw.toMeasure := by
  rw [signLaw_eq_pi]
  exact iIndepFun_pi (fun _ => (measurable_of_countable literalFactor).aemeasurable)

theorem satModel_independent (a : ℝ≥0) (β : ℝ) :
    iIndepFun (fun l (z : InteractionSample 3) => z.2.2.2 l)
      (satModel a β).disorder.toMeasure := by
  have hm (l : Fin 3) : Measurable (fun z : InteractionSample 3 => z.2.2.2 l) := by
    fun_prop
  rw [iIndepFun_iff_map_fun_eq_pi_map (fun l => (hm l).aemeasurable)]
  change Measure.map (fun z : InteractionSample 3 => fun l => z.2.2.2 l)
      (Measure.map (satSample β) signLaw.toMeasure) =
    Measure.pi (fun l => Measure.map (fun z : InteractionSample 3 => z.2.2.2 l)
      (Measure.map (satSample β) signLaw.toMeasure))
  rw [Measure.map_map (Measurable.of_eval hm) (measurable_of_countable _)]
  simp_rw [Measure.map_map (hm _) (measurable_of_countable (satSample β))]
  exact signLaw_independent.map_fun_eq_pi_map
    (fun _ => (measurable_of_countable _).aemeasurable)

theorem satModel_identically_distributed (a : ℝ≥0) (β : ℝ) (l j : Fin 3) :
    IdentDistrib (fun z : InteractionSample 3 => z.2.2.2 l)
      (fun z : InteractionSample 3 => z.2.2.2 j)
      (satModel a β).disorder.toMeasure (satModel a β).disorder.toMeasure := by
  have hm (i : Fin 3) : Measurable (fun z : InteractionSample 3 => z.2.2.2 i) := by
    fun_prop
  refine ⟨(hm l).aemeasurable, (hm j).aemeasurable, ?_⟩
  change Measure.map _ (Measure.map (satSample β) signLaw.toMeasure) =
    Measure.map _ (Measure.map (satSample β) signLaw.toMeasure)
  rw [Measure.map_map (hm l) (measurable_of_countable _),
    Measure.map_map (hm j) (measurable_of_countable _), signLaw_eq_pi]
  change Measure.map (literalFactor ∘ (fun J : Fin 3 → Bool => J l)) _ =
    Measure.map (literalFactor ∘ (fun J : Fin 3 → Bool => J j)) _
  rw [← Measure.map_map (measurable_of_countable literalFactor) (measurable_pi_apply l),
    ← Measure.map_map (measurable_of_countable literalFactor) (measurable_pi_apply j),
    (measurePreserving_eval _ l).map_eq, (measurePreserving_eval _ j).map_eq]

end FixedClauseThreshold.Computability

end OAI
