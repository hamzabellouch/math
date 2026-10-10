import OAI.Probability.FreeIsing.Estimates.RelabelMeasure
import OAI.Probability.FreeIsing.Factors.DiagonalRecovery
import OAI.Probability.FreeIsing.Factors.RecoveryEquivariance
import OAI.Probability.FreeIsing.Factors.Transfer

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace Problem367

theorem exists_ae_equivariant_recovery_of_conditionalCopies
    {W X G : Type*} [MeasurableSpace W] [MeasurableSpace X]
    [MeasurableEq X] [Nonempty X]
    (μ : Measure W) [SFinite μ] (κ : Kernel W X) [IsMarkovKernel κ]
    (T : G → W → W) (S : G → X → X)
    (hT : ∀ g, Measurable (T g)) (hS : ∀ g, Measurable (S g))
    (hjoint : ∀ g, Measure.QuasiMeasurePreserving
      (fun p : W × X => (T g p.1, S g p.2)) (μ ⊗ₘ κ) (μ ⊗ₘ κ))
    (hcopies : ∀ᵐ p ∂μ ⊗ₘ (κ ×ₖ κ), p.2.1 = p.2.2) :
    ∃ F : W → X, Measurable F ∧
      (∀ᵐ w ∂μ, κ w = Measure.dirac (F w)) ∧
      Measure.map F μ = Measure.map Prod.snd (μ ⊗ₘ κ) ∧
      ∀ g, ∀ᵐ w ∂μ, F (T g w) = S g (F w) := by
  obtain ⟨F, hF, hdirac, hgraph⟩ :=
    exists_measurable_recovery_of_conditionalCopies μ κ hcopies
  have hfst : Measure.map Prod.fst (μ ⊗ₘ κ) = μ :=
    Measure.fst_compProd μ κ
  exact ⟨F, hF, hdirac,
    map_eq_second_marginal_of_joint_recovery hfst hF hgraph,
    ae_equivariant_family_of_joint_recovery hfst hT hS hF hjoint hgraph⟩

theorem isFactorOfIID_of_invariant_conditionalCopies {d : ℕ} {theta : ℝ}
    (κ : Kernel (TreeVertex d → ℝ) (TreeVertex d → IsingSpin))
    [IsMarkovKernel κ]
    (hLaw : HasFreeIsingLaw theta
      (Measure.map Prod.snd ((labelMeasure d) ⊗ₘ κ)))
    (hjoint : ∀ g : TreeAut d, Measure.QuasiMeasurePreserving
      (fun p : (TreeVertex d → ℝ) × (TreeVertex d → IsingSpin) =>
        (relabel g p.1, relabel g p.2))
      ((labelMeasure d) ⊗ₘ κ) ((labelMeasure d) ⊗ₘ κ))
    (hcopies : ∀ᵐ p ∂(labelMeasure d) ⊗ₘ (κ ×ₖ κ), p.2.1 = p.2.2) :
    IsFactorOfIID d theta := by
  let : Nonempty (TreeVertex d → IsingSpin) := ⟨fun _ => IsingSpin.pos⟩
  let : IsProbabilityMeasure (labelMeasure d) := by
    unfold labelMeasure
    infer_instance
  obtain ⟨F, hF, _, hmap, heq⟩ :=
    exists_ae_equivariant_recovery_of_conditionalCopies (labelMeasure d) κ
      (fun g : TreeAut d => relabel g) (fun g : TreeAut d => relabel g)
      measurable_relabel measurable_relabel hjoint hcopies
  refine ⟨F, hF, ?_, heq⟩
  rw [hmap]
  exact hLaw

theorem isFactorOfIID_of_invariant_product_conditionalCopies
    {d : ℕ} {theta : ℝ} {α : Type*} [MeasurableSpace α]
    (ν : Measure α) [IsProbabilityMeasure ν]
    (ξ : ℝ → α) (hξ : Measurable ξ) (hξlaw : Measure.map ξ uniform01 = ν)
    (κ : Kernel (TreeVertex d → α) (TreeVertex d → IsingSpin))
    [IsMarkovKernel κ]
    (hLaw : HasFreeIsingLaw theta
      (Measure.map Prod.snd ((Measure.infinitePi (fun _ : TreeVertex d => ν)) ⊗ₘ κ)))
    (hjoint : ∀ g : TreeAut d, Measure.QuasiMeasurePreserving
      (fun p : (TreeVertex d → α) × (TreeVertex d → IsingSpin) =>
        (relabel g p.1, relabel g p.2))
      ((Measure.infinitePi (fun _ : TreeVertex d => ν)) ⊗ₘ κ)
      ((Measure.infinitePi (fun _ : TreeVertex d => ν)) ⊗ₘ κ))
    (hcopies : ∀ᵐ p ∂(Measure.infinitePi (fun _ : TreeVertex d => ν)) ⊗ₘ (κ ×ₖ κ),
      p.2.1 = p.2.2) :
    IsFactorOfIID d theta := by
  let : Nonempty (TreeVertex d → IsingSpin) := ⟨fun _ => IsingSpin.pos⟩
  obtain ⟨F, hF, _, hmap, heq⟩ :=
    exists_ae_equivariant_recovery_of_conditionalCopies
      (Measure.infinitePi (fun _ : TreeVertex d => ν)) κ
      (fun g : TreeAut d => relabel g) (fun g : TreeAut d => relabel g)
      measurable_relabel measurable_relabel hjoint hcopies
  apply isFactorOfIID_of_product_sampler ν ξ hξ hξlaw F hF _ heq
  rw [hmap]
  exact hLaw

end Problem367

end

end OAI
