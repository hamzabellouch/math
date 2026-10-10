import OAI.Probability.FreeIsing.Conditioning.CopyArrayBrownian

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal

namespace Problem367.ConditionalCopyBrownian

variable {E O X : Type*} [MeasurableSpace E] [MeasurableSpace X]

theorem pastPath_comap_mono {s t : ℝ≥0} (hst : s ≤ t) :
    MeasurableSpace.comap (PathSplit.pastPath (E := E) s) inferInstance ≤
      MeasurableSpace.comap (PathSplit.pastPath (E := E) t) inferInstance := by
  let : MeasurableSpace (ℝ≥0 → E) :=
    MeasurableSpace.comap (PathSplit.pastPath (E := E) t)
      (inferInstance : MeasurableSpace (Set.Iic t → E))
  have hm : Measurable (PathSplit.pastPath (E := E) s) := by
    exact measurable_pi_iff.mpr fun u =>
      (measurable_pi_apply (⟨u.1, u.2.trans hst⟩ : Set.Iic t)).comp
        (comap_measurable (PathSplit.pastPath t))
  exact hm.comap_le

theorem joinedPast_eq_sup (s : ℝ≥0) (p : O → X) :
    joinedPast (E := E) s p =
      MeasurableSpace.comap (fun z : (ℝ≥0 → E) × (O × O) => PathSplit.pastPath s z.1) inferInstance ⊔
      (MeasurableSpace.comap (fun z : (ℝ≥0 → E) × (O × O) => p z.2.1) inferInstance ⊔
       MeasurableSpace.comap (fun z : (ℝ≥0 → E) × (O × O) => p z.2.2) inferInstance) := by
  have h : joinedPast (E := E) s p =
      MeasurableSpace.comap (fun z : (ℝ≥0 → E) × (O × O) => PathSplit.pastPath s z.1) inferInstance ⊔
      MeasurableSpace.comap (fun z : (ℝ≥0 → E) × (O × O) => (p z.2.1, p z.2.2)) inferInstance :=
    MeasurableSpace.comap_prodMk _ _
  rw [h]
  congr 1
  exact MeasurableSpace.comap_prodMk _ _

theorem joinedPast_mono {s t : ℝ≥0} (hst : s ≤ t) {p q : O → X}
    (hpq : MeasurableSpace.comap p inferInstance ≤
      MeasurableSpace.comap q inferInstance) :
    joinedPast (E := E) s p ≤ joinedPast t q := by
  rw [joinedPast_eq_sup, joinedPast_eq_sup]
  apply sup_le_sup
  · have h := MeasurableSpace.comap_mono (g := fun z : (ℝ≥0 → E) × (O × O) => z.1)
      (pastPath_comap_mono (E := E) hst)
    simpa only [MeasurableSpace.comap_comp, Function.comp_def] using h
  · apply sup_le_sup
    · have h := MeasurableSpace.comap_mono (g := fun z : (ℝ≥0 → E) × (O × O) => z.2.1) hpq
      simpa only [MeasurableSpace.comap_comp, Function.comp_def] using h
    · have h := MeasurableSpace.comap_mono (g := fun z : (ℝ≥0 → E) × (O × O) => z.2.2) hpq
      simpa only [MeasurableSpace.comap_comp, Function.comp_def] using h

variable [MeasurableSpace O]

def joinedFiltration (past : ℝ≥0 → O → X) (hpast : ∀ s, Measurable (past s))
    (hmono : Monotone (fun s => MeasurableSpace.comap (past s) inferInstance)) :
    Filtration ℝ≥0 (inferInstance : MeasurableSpace ((ℝ≥0 → E) × (O × O))) where
  seq s := joinedPast s (past s)
  mono' := fun _ _ hst => joinedPast_mono hst (hmono hst)
  le' s := joinedPast_le s (hpast s)

@[simp]
theorem joinedFiltration_apply (past : ℝ≥0 → O → X) (hpast : ∀ s, Measurable (past s))
    (hmono : Monotone (fun s => MeasurableSpace.comap (past s) inferInstance)) (s : ℝ≥0) :
    joinedFiltration (E := E) past hpast hmono s = joinedPast s (past s) := rfl

end Problem367.ConditionalCopyBrownian

namespace Problem367.ConditionalCopyArrayBrownian

open ConditionalCopyBrownian

variable {ι O X : Type*} [MeasurableSpace O] [MeasurableSpace X]
variable [StandardBorelSpace X] [Nonempty X]

theorem commonNoise_martingale_joinedFiltration
    (i : ι) (rho : Measure (ℝ≥0 → ι → ℝ)) [IsProbabilityMeasure rho]
    (hB : IsPreBrownianReal (fun t (w : ℝ≥0 → ι → ℝ) => w t i) rho)
    (eta : Kernel (ℝ≥0 → ι → ℝ) O) [IsMarkovKernel eta]
    (past : ℝ≥0 → O → X) (hpast : ∀ s, Measurable (past s))
    (hmono : Monotone (fun s => MeasurableSpace.comap (past s) inferInstance))
    (hind : ∀ s, IndepFun
      (fun q : (ℝ≥0 → ι → ℝ) × O => (PathSplit.pastPath s q.1, past s q.2))
      (fun q => PathSplit.futureIncrements s q.1) (rho ⊗ₘ eta)) :
    Martingale (fun t (q : (ℝ≥0 → ι → ℝ) × (O × O)) => q.1 t i)
      (joinedFiltration past hpast hmono) (rho ⊗ₘ (eta ×ₖ eta)) :=
  commonNoise_martingale i rho hB eta past hpast
    (joinedFiltration past hpast hmono) (fun _ => rfl) hind

theorem isBrownian_commonNoise
    (i : ι) (rho : Measure (ℝ≥0 → ι → ℝ)) [IsProbabilityMeasure rho]
    (hB : IsBrownianReal (fun t (w : ℝ≥0 → ι → ℝ) => w t i) rho)
    (eta : Kernel (ℝ≥0 → ι → ℝ) O) [IsMarkovKernel eta] :
    IsBrownianReal (fun t (q : (ℝ≥0 → ι → ℝ) × (O × O)) => q.1 t i)
      (rho ⊗ₘ (eta ×ₖ eta)) := by
  have hmp : MeasurePreserving (Prod.fst : (ℝ≥0 → ι → ℝ) × (O × O) → (ℝ≥0 → ι → ℝ))
      (rho ⊗ₘ (eta ×ₖ eta)) rho := ⟨measurable_fst, Measure.fst_compProd _ _⟩
  exact ⟨isPreBrownian_commonNoise i rho hB.toIsPreBrownianReal eta,
    hmp.quasiMeasurePreserving.ae hB.cont⟩

end Problem367.ConditionalCopyArrayBrownian

end

end OAI
