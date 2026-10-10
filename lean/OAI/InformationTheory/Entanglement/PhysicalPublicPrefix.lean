import OAI.InformationTheory.Entanglement.PhysicalRightRawPrefix
import OAI.InformationTheory.Entanglement.HilbertRecordMap

namespace OAI

noncomputable section
open scoped InnerProductSpace ComplexOrder MeasureTheory
open ContinuousLinearMap MeasureTheory ProbabilityTheory Filter
namespace SecretKey
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {ι S X : Type*} [MeasurableSpace S] [MeasurableSpace X]

theorem physical_public_raw_prefix (b : HilbertBasis ι ℂ H)
    (μ : Measure S) [IsProbabilityMeasure μ] (κ : Kernel S X) [IsMarkovKernel κ]
    (ρ : S→DensityOperator b)
    (hm : ∀ x y, Measurable (fun h => inner ℂ x ((ρ h).val.val y)))
    (W : PositiveHilbertMeasure (S×X) H b) [IsProbabilityMeasure W.traceMeasure]
    (hEvent : ∀ A B, MeasurableSet A → MeasurableSet B → ∀ x y,
      W.coeff x y (A ×ˢ B)=∫ h in A, ((κ h).real B : ℂ)*inner ℂ x ((ρ h).val.val y) ∂μ) :
    W.traceMeasure=μ ⊗ₘ κ ∧ IsWeakDensity b W (μ ⊗ₘ κ) (ρ ∘ Prod.fst) := by
  let ν := μ ⊗ₘ κ
  let f : S×X→DensityOperator b := ρ ∘ Prod.fst
  have hf : ∀ x y, Measurable (fun p : S×X => inner ℂ x ((f p).val.val y)) :=
    fun x y => (hm x y).comp measurable_fst
  have hd : IsWeakDensity b W ν f := by
    intro Z hZ x y
    have hi := density_coefficient_integrable b ν f hf x y
    have he : W.coeff x y=ν.withDensityᵥ (fun p => inner ℂ x ((f p).val.val y)) := by
      apply complexMeasure_ext_rectangles
      intro A B hA hB
      rw [withDensityᵥ_apply hi (hA.prod hB)]
      change W.coeff x y (A ×ˢ B)=(∫ p in A ×ˢ B, inner ℂ x ((f p).val.val y) ∂(μ ⊗ₘ κ))
      rw [Measure.setIntegral_compProd hA hB hi.integrableOn,hEvent A B hA hB x y]
      apply setIntegral_congr_fun hA
      intro h hh
      change ((κ h).real B : ℂ)*inner ℂ x ((ρ h).val.val y)=∫ _ in B, inner ℂ x ((ρ h).val.val y) ∂κ h
      simp only [integral_const,Measure.restrict_apply_univ,Measure.real,Complex.real_smul]
    rw [he,withDensityᵥ_apply hi hZ]
  exact ⟨weak_density_trace_eq b W ν f hf hd,hd⟩

end SecretKey

end

end OAI
