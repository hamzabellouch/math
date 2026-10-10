import OAI.InformationTheory.Entanglement.ProductInstrumentStep

namespace OAI

noncomputable section
open scoped BigOperators InnerProductSpace ComplexOrder ENNReal MeasureTheory TensorProduct
open ContinuousLinearMap MeasureTheory ProbabilityTheory
namespace SecretKey
variable {S X : Type*} [MeasurableSpace S] [MeasurableSpace X]
lemma compProd_real_rectangle (ν : Measure S) [IsFiniteMeasure ν] (K : Kernel S X)
    [IsMarkovKernel K] {U : Set S} {V : Set X} (hU : MeasurableSet U) (hV : MeasurableSet V) :
    (ν ⊗ₘ K).real (U ×ˢ V)=∫ h in U, (K h).real V ∂ν := by
  rw [Measure.real,Measure.compProd_apply_prod hU hV]
  exact (integral_toReal (K.measurable_coe hV).aemeasurable
    (Filter.Eventually.of_forall (fun h => measure_lt_top (K h) V))).symm
variable {H K L : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  [NormedAddCommGroup L] [InnerProductSpace ℂ L] [CompleteSpace L]
variable {ι κ υ : Type*}

omit [CompleteSpace H] [CompleteSpace L] in
theorem quantum_step_kernel (b : HilbertBasis ι ℂ H) (c : HilbertBasis κ ℂ K)
    (d : HilbertBasis υ ℂ L) (J : S→TraceInstrument b c X)
    (ρ : S→DensityOperator b) (σ : S→DensityOperator d)
    (hm : ∀ V, MeasurableSet V → Measurable (fun h => (J h).outcome (ρ h) V))
    (ν : Measure S) [IsFiniteMeasure ν] (ν' : Measure (S×X)) [IsFiniteMeasure ν']
    (hBorn : ∀ U V, MeasurableSet U → MeasurableSet V →
      ν'.real (U ×ˢ V)=∫ h in U,
        (tensorFunctional (traceClassTrace c) (traceClassTrace d)
          (TensorProduct.map ((J h).event V) LinearMap.id ((ρ h).val ⊗ₜ[ℂ] (σ h).val))).re ∂ν) :
    ν'=ν ⊗ₘ TraceInstrument.historyKernel J ρ hm := by
  apply Measure.ext_prod
  intro U V hU hV
  apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mp
  change ν'.real (U ×ˢ V)=(ν ⊗ₘ TraceInstrument.historyKernel J ρ hm).real (U ×ˢ V)
  rw [hBorn U V hU hV,compProd_real_rectangle ν _ hU hV]
  apply setIntegral_congr_fun hU
  intro h hh
  exact local_product_born b c d (J h) (ρ h) (σ h) hV

omit [CompleteSpace H] [CompleteSpace L] in
lemma right_product_born (b : HilbertBasis ι ℂ H) (c : HilbertBasis κ ℂ K)
    (d : HilbertBasis υ ℂ L) (I : TraceInstrument b c X)
    (ρ : DensityOperator b) (σ : DensityOperator d) {V : Set X} (hV : MeasurableSet V) :
    (tensorFunctional (traceClassTrace d) (traceClassTrace c)
      (TensorProduct.map LinearMap.id (I.event V) (σ.val ⊗ₜ[ℂ] ρ.val))).re=(I.outcome ρ).real V := by
  rw [TensorProduct.map_tmul,tensorFunctional_tmul,LinearMap.id_apply,σ.property.2,one_mul,
    I.outcome_born ρ hV]

end SecretKey

end

end OAI
