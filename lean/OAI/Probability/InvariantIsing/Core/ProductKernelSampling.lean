import OAI.Probability.InvariantIsing.Fields.FieldEndpointProduct

namespace OAI

/-! Coordinatewise sampling commutes with a finite product of root laws. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped BigOperators NNReal

namespace InvariantIsing

lemma product_kernel_comp_general {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {N : ℕ} (κ : Kernel X Y) [IsMarkovKernel κ]
    (K : Kernel (Fin N → X) (Fin N → Y)) [IsMarkovKernel K]
    (hK : ∀ z, K z = Measure.pi (fun i => κ (z i)))
    (ν : Fin N → Measure X) [∀ i, IsProbabilityMeasure (ν i)] :
    K ∘ₘ Measure.pi ν = Measure.pi (fun i => κ ∘ₘ ν i) := by
  apply (Measure.pi_eq (μ := fun i => κ ∘ₘ ν i) ?_).symm
  intro s hs
  suffices hreal : ((K ∘ₘ Measure.pi ν) (univ.pi s)).toReal =
      (∏ i, (κ ∘ₘ ν i) (s i)).toReal by
    have he := congrArg ENNReal.ofReal hreal
    rw [ENNReal.ofReal_toReal (measure_ne_top _ _),
      ENNReal.ofReal_toReal (ENNReal.prod_ne_top (fun i _ => measure_ne_top _ _))] at he
    exact he
  rw [← measureReal_def, kernel_comp_real K (Measure.pi ν) _ (MeasurableSet.univ_pi hs)]
  have he (z : Fin N → X) : (K z).real (univ.pi s) = ∏ i, (κ (z i)).real (s i) := by
    rw [hK, measureReal_def, Measure.pi_pi, ENNReal.toReal_prod]
    rfl
  simp_rw [he]
  change (∫ z : Fin N → X, ∏ i,
    (fun y : X => (κ y).real (s i)) (z i) ∂Measure.pi ν) = _
  rw [integral_fintype_prod_eq_prod (fun i y => (κ y).real (s i)), ENNReal.toReal_prod]
  apply Finset.prod_congr rfl
  intro i _
  exact (kernel_comp_real κ (ν i) (s i) (hs i)).symm

end InvariantIsing

end

end OAI
