import OAI.Probability.FreeIsing.Conditioning.CopyBrownian

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal

namespace Problem367.ConditionalCopyArrayBrownian

open ConditionalCopyBrownian

variable {ι O X : Type*} [MeasurableSpace O] [MeasurableSpace X]
variable [StandardBorelSpace X] [Nonempty X]

theorem condExp_increment_eq_zero
    (i : ι) (rho : Measure (ℝ≥0 → ι → ℝ)) [IsProbabilityMeasure rho]
    (hB : IsPreBrownianReal (fun t (w : ℝ≥0 → ι → ℝ) => w t i) rho)
    (eta : Kernel (ℝ≥0 → ι → ℝ) O) [IsMarkovKernel eta]
    {s t : ℝ≥0} (hst : s ≤ t)
    (past : O → X) (hpast : Measurable past)
    (hind : IndepFun
      (fun q : (ℝ≥0 → ι → ℝ) × O => (PathSplit.pastPath s q.1, past q.2))
      (fun q => PathSplit.futureIncrements s q.1) (rho ⊗ₘ eta)) :
    (rho ⊗ₘ (eta ×ₖ eta))[
      (fun q : (ℝ≥0 → ι → ℝ) × (O × O) => q.1 t i - q.1 s i) |
        joinedPast s past] =ᵐ[rho ⊗ₘ (eta ×ₖ eta)] fun _ => 0 := by
  rcases hst.eq_or_lt with rfl | hst
  · simp
  have hi : Integrable (fun w : ℝ≥0 → ι → ℝ => w t i - w s i) rho :=
    (hB.integrable_eval t).sub (hB.integrable_eval s)
  have hc := condExp_future_eq_integral s rho eta past hpast hind
    (fun z => z ⟨t, hst⟩ i) ((measurable_pi_apply i).comp (measurable_pi_apply _)) hi
  have hz : (∫ w : ℝ≥0 → ι → ℝ, w t i - w s i ∂rho) = 0 := by
    rw [integral_sub (hB.integrable_eval t) (hB.integrable_eval s),
      hB.integral_eval, hB.integral_eval, sub_self]
  simpa only [PathSplit.futureIncrements, Pi.sub_apply, hz] using hc

theorem condExp_increment_sq_eq_elapsed
    (i : ι) (rho : Measure (ℝ≥0 → ι → ℝ)) [IsProbabilityMeasure rho]
    (hB : IsPreBrownianReal (fun t (w : ℝ≥0 → ι → ℝ) => w t i) rho)
    (eta : Kernel (ℝ≥0 → ι → ℝ) O) [IsMarkovKernel eta]
    {s t : ℝ≥0} (hst : s ≤ t)
    (past : O → X) (hpast : Measurable past)
    (hind : IndepFun
      (fun q : (ℝ≥0 → ι → ℝ) × O => (PathSplit.pastPath s q.1, past q.2))
      (fun q => PathSplit.futureIncrements s q.1) (rho ⊗ₘ eta)) :
    (rho ⊗ₘ (eta ×ₖ eta))[
      (fun q : (ℝ≥0 → ι → ℝ) × (O × O) => (q.1 t i - q.1 s i) ^ 2) |
        joinedPast s past] =ᵐ[rho ⊗ₘ (eta ×ₖ eta)]
      fun _ => (t : ℝ) - (s : ℝ) := by
  rcases hst.eq_or_lt with rfl | hst
  · simp
  have hi : Integrable (fun w : ℝ≥0 → ι → ℝ => (w t i - w s i) ^ 2) rho :=
    ((hB.isGaussianProcess.hasGaussianLaw_eval t).memLp_two.sub
      (hB.isGaussianProcess.hasGaussianLaw_eval s).memLp_two).integrable_sq
  have hc := condExp_future_eq_integral s rho eta past hpast hind
    (fun z => (z ⟨t, hst⟩ i) ^ 2) (((measurable_pi_apply i).comp (measurable_pi_apply _)).pow_const 2) hi
  have hz : (∫ w : ℝ≥0 → ι → ℝ, (w t i - w s i) ^ 2 ∂rho) = (t : ℝ) - (s : ℝ) := by
    have h := preBrownian_integral_sq (hB.shift s) (t - s)
    simpa [add_tsub_cancel_of_le hst.le, NNReal.coe_sub hst.le] using h
  simpa only [PathSplit.futureIncrements, Pi.sub_apply, hz] using hc

theorem isPreBrownian_commonNoise
    (i : ι) (rho : Measure (ℝ≥0 → ι → ℝ)) [IsProbabilityMeasure rho]
    (hB : IsPreBrownianReal (fun t (w : ℝ≥0 → ι → ℝ) => w t i) rho)
    (eta : Kernel (ℝ≥0 → ι → ℝ) O) [IsMarkovKernel eta] :
    IsPreBrownianReal (fun t (q : (ℝ≥0 → ι → ℝ) × (O × O)) => q.1 t i)
      (rho ⊗ₘ (eta ×ₖ eta)) := by
  have hmp : MeasurePreserving (Prod.fst : (ℝ≥0 → ι → ℝ) × (O × O) → (ℝ≥0 → ι → ℝ))
      (rho ⊗ₘ (eta ×ₖ eta)) rho := ⟨measurable_fst, Measure.fst_compProd _ _⟩
  exact ⟨fun I => (hB.hasLaw I).comp hmp.hasLaw⟩

theorem commonNoise_martingale
    (i : ι) (rho : Measure (ℝ≥0 → ι → ℝ)) [IsProbabilityMeasure rho]
    (hB : IsPreBrownianReal (fun t (w : ℝ≥0 → ι → ℝ) => w t i) rho)
    (eta : Kernel (ℝ≥0 → ι → ℝ) O) [IsMarkovKernel eta]
    (past : ℝ≥0 → O → X) (hpast : ∀ s, Measurable (past s))
    (G : Filtration ℝ≥0 (inferInstance : MeasurableSpace ((ℝ≥0 → ι → ℝ) × (O × O))))
    (hG : ∀ s, G s = joinedPast s (past s))
    (hind : ∀ s, IndepFun
      (fun q : (ℝ≥0 → ι → ℝ) × O => (PathSplit.pastPath s q.1, past s q.2))
      (fun q => PathSplit.futureIncrements s q.1) (rho ⊗ₘ eta)) :
    Martingale (fun t (q : (ℝ≥0 → ι → ℝ) × (O × O)) => q.1 t i) G
      (rho ⊗ₘ (eta ×ₖ eta)) := by
  have had : StronglyAdapted G
      (fun t (q : (ℝ≥0 → ι → ℝ) × (O × O)) => q.1 t i) := by
    intro t
    rw [hG t]
    have hh : Measurable[joinedPast (E := ι → ℝ) t (past t)]
        (joinedHistory (E := ι → ℝ) t (past t)) :=
      comap_measurable _
    exact ((measurable_pi_apply i).comp ((measurable_pi_apply
      (⟨t, by simp⟩ : Set.Iic t)).comp (measurable_fst.comp hh))).stronglyMeasurable
  apply martingale_of_conditional_increment_zero had
    (fun t => (isPreBrownian_commonNoise i rho hB eta).integrable_eval t)
  intro s t hst
  rw [hG s]
  exact condExp_increment_eq_zero i rho hB eta hst (past s) (hpast s) (hind s)

end Problem367.ConditionalCopyArrayBrownian

end

end OAI
