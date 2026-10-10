import OAI.Probability.FreeIsing.Conditioning.Pullback
import OAI.Probability.FreeIsing.Estimates.TwoSeparatorRegression
import OAI.Probability.FreeIsing.Trees.RootRegression

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace Problem367

theorem HasFreeIsingLaw.condExp_spin_given_adj
    {d : ℕ} {theta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw theta μ) (h0 : -1 ≤ theta)
    {u v : TreeVertex d} (huv : treeAdj u v) :
    ∀ x, μ[(fun y => spinSign (y u)) |
      isingSpinMeasurable.comap (fun y => y v)] x = theta * spinSign (x v) := by
  let := hμ.isProbabilityMeasure
  have hi : Integrable (fun y : TreeVertex d → IsingSpin => spinSign (y u)) μ := by
    simpa only [IsingSpin.toReal_eq_spinSign] using integrable_spin μ u
  have h := BinaryRegression.condExp_eq_cov_mul_spinSign (measurable_pi_apply v)
    (hμ.marginal v) hi (hμ.integral_spinSign u)
  simpa only [hμ.integral_edge_spinSign h0 huv] using h

theorem HasFreeIsingLaw.condExp_planted_spin_given_adj
    {d : ℕ} {theta : ℝ} {A : Type*} [MeasurableSpace A]
    {μ : Measure (TreeVertex d → IsingSpin)} (hμ : HasFreeIsingLaw theta μ)
    (h0 : -1 ≤ theta) (ν : Measure A) [IsProbabilityMeasure ν]
    {u v : TreeVertex d} (huv : treeAdj u v) :
    (μ.prod ν)[(fun z : (TreeVertex d → IsingSpin) × A => spinSign (z.1 u)) |
      isingSpinMeasurable.comap (fun z => z.1 v)] =ᵐ[μ.prod ν]
        fun z => theta * spinSign (z.1 v) := by
  let := hμ.isProbabilityMeasure
  have hi : Integrable (fun y : TreeVertex d → IsingSpin => spinSign (y u)) μ := by
    simpa only [IsingSpin.toReal_eq_spinSign] using integrable_spin μ u
  have h := condExp_comp_measurePreserving (μ.prod ν) μ Prod.fst
    measurePreserving_fst (isingSpinMeasurable.comap (fun y => y v))
    (measurable_pi_apply v).comap_le hi
  simpa only [MeasurableSpace.comap_comp, Function.comp_def,
    hμ.condExp_spin_given_adj h0 huv] using h

theorem HasFreeIsingLaw.condExp_planted_spin_of_separator
    {d : ℕ} {theta : ℝ} {A C : Type*}
    [MeasurableSpace A] [StandardBorelSpace A]
    [mC : MeasurableSpace C] [StandardBorelSpace C] [Nonempty C]
    {μ : Measure (TreeVertex d → IsingSpin)} [IsFiniteMeasure μ]
    (hμ : HasFreeIsingLaw theta μ) (h0 : -1 ≤ theta)
    (ν : Measure A) [IsProbabilityMeasure ν]
    {u v : TreeVertex d} (huv : treeAdj u v)
    {S : (TreeVertex d → IsingSpin) × A → C} (hS : Measurable S)
    (hind : CondIndepFun
      (isingSpinMeasurable.comap (fun z : (TreeVertex d → IsingSpin) × A => z.1 v))
      ((measurable_pi_apply v).comp measurable_fst).comap_le S
      (fun z => spinSign (z.1 u)) (μ.prod ν)) :
    (μ.prod ν)[(fun z : (TreeVertex d → IsingSpin) × A => spinSign (z.1 u)) |
      mC.comap S] =ᵐ[μ.prod ν]
        fun z => theta * (μ.prod ν)[(fun z => spinSign (z.1 v)) | mC.comap S] z := by
  let := hμ.isProbabilityMeasure
  have hi : Integrable (fun y : TreeVertex d → IsingSpin => spinSign (y u)) μ := by
    simpa only [IsingSpin.toReal_eq_spinSign] using integrable_spin μ u
  have hm : Measurable (fun z : (TreeVertex d → IsingSpin) × A => spinSign (z.1 u)) :=
    measurable_spinToReal.comp ((measurable_pi_apply u).comp measurable_fst)
  have hsep := condExp_condExp_eq_of_separator hS
    ((measurable_pi_apply v).comp measurable_fst) hm (hi.comp_fst ν) hind
  refine hsep.symm.trans ((condExp_congr_ae (m := mC.comap S)
    (hμ.condExp_planted_spin_given_adj h0 ν huv)).trans ?_)
  simpa only [Pi.smul_def, smul_eq_mul] using
    (condExp_smul (μ := μ.prod ν) theta
      (fun z : (TreeVertex d → IsingSpin) × A => spinSign (z.1 v)) (mC.comap S))

end Problem367

end

end OAI
