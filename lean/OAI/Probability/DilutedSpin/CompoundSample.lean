import OAI.Probability.DilutedSpin.InsertionPoint
import OAI.Probability.DilutedSpin.RootProductLaw

namespace OAI

section
namespace DilutedSpinGlass
open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory
open scoped NNReal BigOperators
variable {X E : Type} [MeasurableSpace X]
    [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E]

lemma measurable_compound_sample (V : X → E) (hV : Measurable V) :
    Measurable (fun z : Sigma (RootPath X) => ∑ i,V (rootArray z.1 z.2 i)) := by
  apply measurable_sigmaUncurry (f := fun n z => ∑ i,V (rootArray n z i))
  intro n
  apply Finset.measurable_sum
  intro i _
  exact hV.comp (measurable_rootArray n i)

lemma compound_sample_integrable (μ : Measure X) [IsProbabilityMeasure μ]
    (V : X → E) (hV : Measurable V) (r : ℝ≥0) {c : ℝ≥0} {F : E → ℝ}
    (hF : LipschitzWith c F) (hVi : Integrable V μ) :
    Integrable (fun z : Sigma (RootPath X) => F (∑ i,V (rootArray z.1 z.2 i)))
      (compoundRootLaw μ r) := by
  have : IsProbabilityMeasure (Measure.map V μ) :=
    (Measure.isProbabilityMeasure_map_iff hV.aemeasurable).mpr inferInstance
  have hiV : Integrable id (Measure.map V μ) :=
    (integrable_map_measure measurable_id.aestronglyMeasurable hV.aemeasurable).mpr hVi
  have hi := integrable_lipschitz_of_id (compoundPoisson r (Measure.map V μ))
    (compoundPoisson_integrable_id r _ hiV) hF
  rw [← map_compoundRoot_energy μ V hV r] at hi
  exact (integrable_map_measure hF.continuous.aestronglyMeasurable
    (measurable_compound_sample V hV).aemeasurable).mp hi

lemma integral_compound_sample (μ : Measure X) [IsProbabilityMeasure μ]
    (V : X → E) (hV : Measurable V) (r : ℝ≥0) {c : ℝ≥0} {F : E → ℝ}
    (hF : LipschitzWith c F) (hVi : Integrable V μ) :
    (∫ E,F E ∂compoundPoisson r (Measure.map V μ))=
      ∫ k,∫ z : RootPath X k,F (∑ i,V (rootArray k z i)) ∂rootLaw k (fun _ => μ) ∂poissonMeasure r := by
  rw [← map_compoundRoot_energy μ V hV r,
    integral_map (measurable_compound_sample V hV).aemeasurable hF.continuous.aestronglyMeasurable]
  exact integral_familyLaw (poissonMeasure r) (fun k => rootLaw k (fun _ => μ))
    (fun k z => F (∑ i,V (rootArray k z i)))
    (fun k => by
      apply hF.continuous.measurable.comp
      apply Finset.measurable_sum
      intro i _
      exact hV.comp (measurable_rootArray k i))
    (compound_sample_integrable μ V hV r hF hVi)

omit [MeasurableSpace X] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in
lemma iid_sample_norm_bound (V : X → E) {C : ℝ} (hV : ∀ x,‖V x‖≤C)
    (k : ℕ) (z : RootPath X k) : ‖∑ i,V (rootArray k z i)‖≤C*k := by
  calc
    _ ≤ ∑ i : Fin k,‖V (rootArray k z i)‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Fin k,C := Finset.sum_le_sum (fun _ _ => hV _)
    _ = _ := by simp [mul_comm]

lemma integral_compound_finite_sample {J : Type} [Fintype J] [Nonempty J]
    [MeasurableSpace J] [MeasurableSingletonClass J]
    (μ : Measure X) [IsProbabilityMeasure μ] (V : X×J → E) (hV : Measurable V)
    {C : ℝ} (hVb : ∀ x,‖V x‖≤C) (r : ℝ≥0) {c : ℝ≥0} {F : E → ℝ}
    (hF : LipschitzWith c F) :
    (∫ E,F E ∂compoundPoisson r (Measure.map V (μ.prod (finiteUniform J))))=
      ∫ k,∫ z : Fin k → X,(FiniteLaw.uniform : FiniteLaw (Fin k → J)).expect
        (fun j => F (∑ i,V (z i,j i))) ∂Measure.pi (fun _ : Fin k => μ) ∂poissonMeasure r := by
  rw [integral_compound_sample (μ.prod (finiteUniform J)) V hV r hF
    (Integrable.of_bound hV.aestronglyMeasurable C (ae_of_all _ hVb))]
  apply integral_congr_ae
  filter_upwards [] with k
  apply integral_root_prod_finite μ k (fun z => F (∑ i,V (z.1 i,z.2 i)))
  · apply hF.continuous.measurable.comp
    exact Finset.measurable_sum _ (fun i _ => hV.comp
      (((measurable_pi_apply i).comp measurable_fst).prodMk ((measurable_pi_apply i).comp measurable_snd)))
  · intro z
    have hn : ‖∑ i : Fin k,V (z.1 i,z.2 i)‖ ≤ C*k := by
      calc
        _ ≤ ∑ i : Fin k,‖V (z.1 i,z.2 i)‖ := norm_sum_le _ _
        _ ≤ ∑ _i : Fin k,C := Finset.sum_le_sum (fun _ _ => hVb _)
        _ = _ := by simp [mul_comm]
    have hh := hF.dist_le_mul (∑ i,V (z.1 i,z.2 i)) 0
    simp only [dist_eq_norm,sub_zero,Real.norm_eq_abs] at hh
    calc
      _ = |F (∑ i,V (z.1 i,z.2 i))-F 0+F 0| := by rw [sub_add_cancel]
      _ ≤ |F (∑ i,V (z.1 i,z.2 i))-F 0|+|F 0| := abs_add_le _ _
      _ ≤ (c:ℝ)*(C*k)+|F 0| := add_le_add (hh.trans
        (mul_le_mul_of_nonneg_left hn c.coe_nonneg)) le_rfl

end DilutedSpinGlass

end

end OAI
