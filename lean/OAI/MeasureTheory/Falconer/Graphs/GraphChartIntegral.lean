import OAI.MeasureTheory.Falconer.Graphs.GraphCartesianSubstitution

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory

theorem graphLiftMap_integral (S : Set GraphLiftSpace) (hS : MeasurableSet S)
    (f : GraphLiftSpace → ℂ) :
    (∫ q in graphLiftMap '' S, f q) =
      ∫ p in S, (Real.sqrt (1+(p 2)^2))⁻¹ • f (graphLiftMap p) := by
  have he := integral_image_eq_integral_abs_det_fderiv_smul volume hS
    (fun p (_ : p ∈ S) => (graphLiftMap_hasFDerivAt p).hasFDerivWithinAt)
    graphLiftMap_injective.injOn f
  simpa only [graphLiftDerivative_det, abs_neg, abs_of_nonneg
    (inv_nonneg.mpr (Real.sqrt_nonneg _))] using he

theorem graphPolarMap_integral (S : Set GraphLiftSpace) (hS : MeasurableSet S)
    (hdom : S ⊆ graphPolarDomain) (f : GraphLiftSpace → ℂ) :
    (∫ x in graphPolarMap '' S, f x) = ∫ p in S, p 0 • f (graphPolarMap p) := by
  rw [integral_image_eq_integral_abs_det_fderiv_smul volume hS
    (fun p (_ : p ∈ S) => (graphPolarMap_hasFDerivAt p).hasFDerivWithinAt)
    (graphPolarMap_injOn.mono hdom)]
  apply setIntegral_congr_fun hS
  intro p hp
  dsimp only
  rw [graphPolarDerivative_det,abs_of_pos (hdom hp).1]

theorem graph_chart_weighted_pullback (f : GraphLiftSpace → ℂ)
    {p : GraphLiftSpace} (hp : p ∈ graphPolarDomain) :
    |(graphPolarDerivative p).det| • (graphJacobianWeight (graphPolarMap p) •
      f (graphLiftMap (graphPolarInverse (graphPolarMap p)))) =
      |(graphLiftDerivative p).det| • f (graphLiftMap p) := by
  rw [graphPolarInverse_left hp, graphJacobianWeight_polar hp,
    graphPolarDerivative_det,abs_of_pos hp.1,graphLiftDerivative_det,abs_neg,
    abs_of_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _)),smul_smul]
  congr 1
  have hr := hp.1.ne'
  have hs : Real.sqrt (1+(p 2)^2) ≠ 0 := by positivity
  field_simp

theorem graph_chart_cartesian_integral (S : Set GraphLiftSpace) (hS : MeasurableSet S)
    (hdom : S ⊆ graphPolarDomain) (f : GraphLiftSpace → ℂ) :
    (∫ q in graphLiftMap '' S, f q) =
      ∫ x in graphPolarMap '' S, graphJacobianWeight x •
        f (graphLiftMap (graphPolarInverse x)) := by
  rw [integral_image_eq_integral_abs_det_fderiv_smul volume hS
    (fun p (_ : p ∈ S) => (graphLiftMap_hasFDerivAt p).hasFDerivWithinAt)
    graphLiftMap_injective.injOn,
    integral_image_eq_integral_abs_det_fderiv_smul volume hS
    (fun p (_ : p ∈ S) => (graphPolarMap_hasFDerivAt p).hasFDerivWithinAt)
    (graphPolarMap_injOn.mono hdom)]
  exact setIntegral_congr_fun hS (fun p hp => (graph_chart_weighted_pullback f (hdom hp)).symm)

theorem graph_chart_cartesian_integrable_iff (S : Set GraphLiftSpace) (hS : MeasurableSet S)
    (hdom : S ⊆ graphPolarDomain) (f : GraphLiftSpace → ℂ) :
    IntegrableOn f (graphLiftMap '' S) ↔
      IntegrableOn (fun x => graphJacobianWeight x • f (graphLiftMap (graphPolarInverse x)))
        (graphPolarMap '' S) := by
  rw [integrableOn_image_iff_integrableOn_abs_det_fderiv_smul volume hS
    (fun p (_ : p ∈ S) => (graphLiftMap_hasFDerivAt p).hasFDerivWithinAt)
    graphLiftMap_injective.injOn,
    integrableOn_image_iff_integrableOn_abs_det_fderiv_smul volume hS
    (fun p (_ : p ∈ S) => (graphPolarMap_hasFDerivAt p).hasFDerivWithinAt)
    (graphPolarMap_injOn.mono hdom)]
  apply integrableOn_congr_fun
  · intro p hp
    exact (graph_chart_weighted_pullback f (hdom hp)).symm
  · exact hS

end PlanarFalconer

end OAI
