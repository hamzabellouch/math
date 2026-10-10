import OAI.InformationTheory.Entanglement.TraceStateBounds
import OAI.InformationTheory.Entanglement.QuantumStepKernel

namespace OAI

noncomputable section
open scoped BigOperators InnerProductSpace ComplexOrder ENNReal MeasureTheory TensorProduct
open ContinuousLinearMap MeasureTheory ProbabilityTheory
namespace SecretKey
variable {S X : Type*} [MeasurableSpace S] [MeasurableSpace X]
variable {H K L : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  [NormedAddCommGroup L] [InnerProductSpace ℂ L] [CompleteSpace L]
variable {ι κ υ : Type*}
lemma complexMeasure_ext_rectangles {M N : ComplexMeasure (S×X)}
    (h : ∀ U V, MeasurableSet U → MeasurableSet V → M (U ×ˢ V)=N (U ×ˢ V)) : M=N := by
  apply VectorMeasure.ext_of_generateFrom _ _ generateFrom_prod.symm isPiSystem_prod
  · rw [← Set.univ_prod_univ]
    exact h _ _ MeasurableSet.univ MeasurableSet.univ
  · rintro - ⟨U,hU,V,hV,rfl⟩
    exact h U V hU hV

lemma product_density_integrable (b : HilbertBasis ι ℂ H) (d : HilbertBasis υ ℂ L)
    {Ω : Type*} [MeasurableSpace Ω] (ν : Measure Ω) [IsFiniteMeasure ν]
    (ρ : Ω→DensityOperator b) (σ : Ω→DensityOperator d)
    (x y : H) (u v : L)
    (hm : Measurable (fun z => inner ℂ x ((ρ z).val.val y)*inner ℂ u ((σ z).val.val v))) :
    Integrable (fun z => inner ℂ x ((ρ z).val.val y)*inner ℂ u ((σ z).val.val v)) ν := by
  apply (integrable_const (‖x‖*‖y‖*(‖u‖*‖v‖))).mono' hm.aestronglyMeasurable
  filter_upwards with z
  rw [norm_mul]
  exact mul_le_mul (density_coefficient_bound b (ρ z) x y)
    (density_coefficient_bound d (σ z) u v) (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))

omit [CompleteSpace H] in
theorem local_refinement_product_density (b : HilbertBasis ι ℂ H) (c : HilbertBasis κ ℂ K)
    (d : HilbertBasis υ ℂ L) (J : S→TraceInstrument b c X)
    (ρ : S→DensityOperator b) (σ : S→DensityOperator d)
    (hm : ∀ V, MeasurableSet V → Measurable (fun h => (J h).outcome (ρ h) V))
    (U : ∀ h, (J h).ConditionalUpdate (ρ h))
    (ν : Measure S) [IsFiniteMeasure ν]
    (x y : K) (u v : L)
    (hf : Measurable (fun p : S×X => inner ℂ x (((U p.1).state p.2).val.val y)*
      inner ℂ u ((σ p.1).val.val v)))
    (M : ComplexMeasure (S×X))
    (hEvent : ∀ A B, MeasurableSet A → MeasurableSet B → M (A ×ˢ B)=
      ∫ h in A, tensorFunctional (traceClassCoefficient c x y) (traceClassCoefficient d u v)
        (TensorProduct.map ((J h).event B) LinearMap.id ((ρ h).val ⊗ₜ[ℂ] (σ h).val)) ∂ν) :
    M=(ν ⊗ₘ TraceInstrument.historyKernel J ρ hm).withDensityᵥ
      (fun p : S×X => inner ℂ x (((U p.1).state p.2).val.val y)*inner ℂ u ((σ p.1).val.val v)) := by
  let k := TraceInstrument.historyKernel J ρ hm
  have hi := product_density_integrable c d (ν ⊗ₘ k)
    (fun p : S×X => (U p.1).state p.2) (fun p : S×X => σ p.1) x y u v hf
  apply complexMeasure_ext_rectangles
  intro A B hA hB
  rw [withDensityᵥ_apply hi (hA.prod hB),Measure.setIntegral_compProd hA hB hi.integrableOn,hEvent A B hA hB]
  apply setIntegral_congr_fun hA
  intro h hh
  exact local_product_disintegration b c d (J h) (ρ h) (σ h) (U h) hB x y u v

end SecretKey

end

end OAI
