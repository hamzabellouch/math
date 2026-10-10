import OAI.Probability.FreeIsing.Brownian.Martingale
import OAI.Probability.FreeIsing.Martingales.InnovationMartingale
import OAI.Probability.FreeIsing.Trees.PathSplit

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal

namespace Problem367.ConditionalCopyBrownian

variable {O X E : Type*} [MeasurableSpace O] [MeasurableSpace X] [MeasurableSpace E]

def joinedHistory (s : ℝ≥0) (past : O → X)
    (q : (ℝ≥0 → E) × (O × O)) : (Set.Iic s → E) × (X × X) :=
  (PathSplit.pastPath s q.1, (past q.2.1, past q.2.2))

theorem measurable_joinedHistory (s : ℝ≥0) {past : O → X}
    (hpast : Measurable past) : Measurable (joinedHistory (E := E) s past) := by
  exact ((PathSplit.measurable_pastPath s).comp measurable_fst).prodMk
    ((hpast.comp (measurable_fst.comp measurable_snd)).prodMk
      (hpast.comp (measurable_snd.comp measurable_snd)))

abbrev joinedPast (s : ℝ≥0) (past : O → X) :
    MeasurableSpace ((ℝ≥0 → E) × (O × O)) :=
  MeasurableSpace.comap (joinedHistory s past) inferInstance

theorem joinedPast_le (s : ℝ≥0) {past : O → X} (hpast : Measurable past) :
    joinedPast s past ≤ (inferInstance : MeasurableSpace ((ℝ≥0 → E) × (O × O))) :=
  (measurable_joinedHistory s hpast).comap_le

variable [StandardBorelSpace X] [Nonempty X]

theorem condExp_future_eq_integral
    [AddCommGroup E] [MeasurableAdd₂ E] [MeasurableSub₂ E]
    (s : ℝ≥0) (rho : Measure (ℝ≥0 → E)) [IsProbabilityMeasure rho]
    (eta : Kernel (ℝ≥0 → E) O) [IsMarkovKernel eta]
    (past : O → X) (hpast : Measurable past)
    (hind : IndepFun
      (fun q : (ℝ≥0 → E) × O => (PathSplit.pastPath s q.1, past q.2))
      (fun q => PathSplit.futureIncrements s q.1) (rho ⊗ₘ eta))
    (f : (Set.Ioi s → E) → ℝ) (hf : Measurable f)
    (hfint : Integrable (fun w => f (PathSplit.futureIncrements s w)) rho) :
    (rho ⊗ₘ (eta ×ₖ eta))[
      (fun q : (ℝ≥0 → E) × (O × O) => f (PathSplit.futureIncrements s q.1)) |
        joinedPast s past] =ᵐ[rho ⊗ₘ (eta ×ₖ eta)]
      fun _ => ∫ w, f (PathSplit.futureIncrements s w) ∂rho := by
  have hi := (PathSplit.indepFun_future_conditionalCopies s rho eta past hpast hind).symm.comp
    hf measurable_id
  have hfm : Measurable (fun q : (ℝ≥0 → E) × (O × O) =>
      f (PathSplit.futureIncrements s q.1)) :=
    hf.comp ((PathSplit.measurable_futureIncrements s).comp measurable_fst)
  have hce := condExp_indep_eq hfm.comap_le (joinedPast_le s hpast)
    (measurable_iff_comap_le.mpr le_rfl).stronglyMeasurable hi
  have hmp : MeasurePreserving (Prod.fst : (ℝ≥0 → E) × (O × O) → (ℝ≥0 → E))
      (rho ⊗ₘ (eta ×ₖ eta)) rho := ⟨measurable_fst, Measure.fst_compProd _ _⟩
  have hint := hmp.integrable_comp_of_integrable hfint
  have hmean : (∫ q : (ℝ≥0 → E) × (O × O),
      f (PathSplit.futureIncrements s q.1) ∂rho ⊗ₘ (eta ×ₖ eta)) =
      ∫ w, f (PathSplit.futureIncrements s w) ∂rho := by
    simpa only [Function.comp_apply, integral_const, probReal_univ,
      one_smul] using (Measure.integral_compProd hint)
  simpa only [Function.comp_def, hmean] using hce

theorem condExp_increment_eq_zero
    (rho : Measure (ℝ≥0 → ℝ)) [IsProbabilityMeasure rho]
    (hB : IsPreBrownianReal (fun t (w : ℝ≥0 → ℝ) => w t) rho)
    (eta : Kernel (ℝ≥0 → ℝ) O) [IsMarkovKernel eta]
    {s t : ℝ≥0} (hst : s ≤ t)
    (past : O → X) (hpast : Measurable past)
    (hind : IndepFun
      (fun q : (ℝ≥0 → ℝ) × O => (PathSplit.pastPath s q.1, past q.2))
      (fun q => PathSplit.futureIncrements s q.1) (rho ⊗ₘ eta)) :
    (rho ⊗ₘ (eta ×ₖ eta))[
      (fun q : (ℝ≥0 → ℝ) × (O × O) => q.1 t - q.1 s) |
        joinedPast s past] =ᵐ[rho ⊗ₘ (eta ×ₖ eta)] fun _ => 0 := by
  rcases hst.eq_or_lt with rfl | hst
  · simp
  have hi : Integrable (fun w : ℝ≥0 → ℝ => w t - w s) rho :=
    (hB.integrable_eval t).sub (hB.integrable_eval s)
  have hc := condExp_future_eq_integral s rho eta past hpast hind
    (fun z => z ⟨t, hst⟩) (measurable_pi_apply _) hi
  have hz : (∫ w : ℝ≥0 → ℝ, w t - w s ∂rho) = 0 := by
    rw [integral_sub (hB.integrable_eval t) (hB.integrable_eval s),
      hB.integral_eval, hB.integral_eval, sub_self]
  simpa only [PathSplit.futureIncrements, hz] using hc

theorem condExp_increment_sq_eq_elapsed
    (rho : Measure (ℝ≥0 → ℝ)) [IsProbabilityMeasure rho]
    (hB : IsPreBrownianReal (fun t (w : ℝ≥0 → ℝ) => w t) rho)
    (eta : Kernel (ℝ≥0 → ℝ) O) [IsMarkovKernel eta]
    {s t : ℝ≥0} (hst : s ≤ t)
    (past : O → X) (hpast : Measurable past)
    (hind : IndepFun
      (fun q : (ℝ≥0 → ℝ) × O => (PathSplit.pastPath s q.1, past q.2))
      (fun q => PathSplit.futureIncrements s q.1) (rho ⊗ₘ eta)) :
    (rho ⊗ₘ (eta ×ₖ eta))[
      (fun q : (ℝ≥0 → ℝ) × (O × O) => (q.1 t - q.1 s) ^ 2) |
        joinedPast s past] =ᵐ[rho ⊗ₘ (eta ×ₖ eta)]
      fun _ => (t : ℝ) - (s : ℝ) := by
  rcases hst.eq_or_lt with rfl | hst
  · simp
  have hi : Integrable (fun w : ℝ≥0 → ℝ => (w t - w s) ^ 2) rho :=
    ((hB.isGaussianProcess.hasGaussianLaw_eval t).memLp_two.sub
      (hB.isGaussianProcess.hasGaussianLaw_eval s).memLp_two).integrable_sq
  have hc := condExp_future_eq_integral s rho eta past hpast hind
    (fun z => (z ⟨t, hst⟩) ^ 2) ((measurable_pi_apply _).pow_const 2) hi
  have hz : (∫ w : ℝ≥0 → ℝ, (w t - w s) ^ 2 ∂rho) = (t : ℝ) - (s : ℝ) := by
    have h := preBrownian_integral_sq (hB.shift s) (t - s)
    simpa [add_tsub_cancel_of_le hst.le, NNReal.coe_sub hst.le] using h
  simpa only [PathSplit.futureIncrements, hz] using hc

theorem isPreBrownian_commonNoise
    (rho : Measure (ℝ≥0 → ℝ)) [IsProbabilityMeasure rho]
    (hB : IsPreBrownianReal (fun t (w : ℝ≥0 → ℝ) => w t) rho)
    (eta : Kernel (ℝ≥0 → ℝ) O) [IsMarkovKernel eta] :
    IsPreBrownianReal (fun t (q : (ℝ≥0 → ℝ) × (O × O)) => q.1 t)
      (rho ⊗ₘ (eta ×ₖ eta)) := by
  have hmp : MeasurePreserving (Prod.fst : (ℝ≥0 → ℝ) × (O × O) → (ℝ≥0 → ℝ))
      (rho ⊗ₘ (eta ×ₖ eta)) rho := ⟨measurable_fst, Measure.fst_compProd _ _⟩
  exact ⟨fun I => (hB.hasLaw I).comp hmp.hasLaw⟩

theorem commonNoise_martingale
    (rho : Measure (ℝ≥0 → ℝ)) [IsProbabilityMeasure rho]
    (hB : IsPreBrownianReal (fun t (w : ℝ≥0 → ℝ) => w t) rho)
    (eta : Kernel (ℝ≥0 → ℝ) O) [IsMarkovKernel eta]
    (past : ℝ≥0 → O → X) (hpast : ∀ s, Measurable (past s))
    (G : Filtration ℝ≥0 (inferInstance : MeasurableSpace ((ℝ≥0 → ℝ) × (O × O))))
    (hG : ∀ s, G s = joinedPast s (past s))
    (hind : ∀ s, IndepFun
      (fun q : (ℝ≥0 → ℝ) × O => (PathSplit.pastPath s q.1, past s q.2))
      (fun q => PathSplit.futureIncrements s q.1) (rho ⊗ₘ eta)) :
    Martingale (fun t (q : (ℝ≥0 → ℝ) × (O × O)) => q.1 t) G
      (rho ⊗ₘ (eta ×ₖ eta)) := by
  have had : StronglyAdapted G
      (fun t (q : (ℝ≥0 → ℝ) × (O × O)) => q.1 t) := by
    intro t
    rw [hG t]
    have hh : Measurable[joinedPast (E := ℝ) t (past t)]
        (joinedHistory (E := ℝ) t (past t)) :=
      comap_measurable _
    exact ((measurable_pi_apply (⟨t, by simp⟩ : Set.Iic t)).comp
      (measurable_fst.comp hh)).stronglyMeasurable
  apply martingale_of_conditional_increment_zero had
    (fun t => (isPreBrownian_commonNoise rho hB eta).integrable_eval t)
  intro s t hst
  rw [hG s]
  exact condExp_increment_eq_zero rho hB eta hst (past s) (hpast s) (hind s)

end Problem367.ConditionalCopyBrownian

end

end OAI
