import OAI.GroupTheory.PolycyclicRecognition.Algebra.DynkinJacobian
import OAI.GroupTheory.PolycyclicRecognition.Analysis.JacobianMeasure
import Mathlib.MeasureTheory.Group.Measure

namespace OAI

/-! # Haar measure derived from a finite BCH chart

The global chart and its group multiplication formula suffice: the Jacobian
of every left translation is one because its nonconstant part raises the
lower central series. No Haar compatibility is assumed.
-/

noncomputable section
namespace PolycyclicRecognition

open MeasureTheory LieModule

variable {L : Type*} [RealNormedLieAlgebra L] [FiniteDimensional ℝ L]
  [MeasurableSpace L] [BorelSpace L]
  {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G]

theorem dynkin_chart_map_isHaar
    (chart : L ≃ₜ G) (hzero : chart 0 = 1)
    {c : ℕ} (coeff : DynkinCoefficients c 2)
    (hprod : ∀ x y, chart x * chart y = chart (finiteDynkinPolynomial coeff ![x, y]))
    {d : ℕ} (hd : lowerCentralSeries ℝ L L d = ⊥)
    (μ : Measure L) [μ.IsAddHaarMeasure] : (Measure.map chart μ).IsHaarMeasure := by
  have hunit : ∀ y : L, finiteDynkinPolynomial coeff ![0, y] = y := by
    intro y
    apply chart.injective
    rw [← hprod, hzero, one_mul]
  apply homeomorph_map_isHaar_of_translations chart μ
  intro g
  have heq : (fun z => chart.symm (g * chart z)) =
      fun z => finiteDynkinPolynomial coeff ![chart.symm g, z] := by
    funext z
    apply chart.injective
    simp only [chart.apply_symm_apply, ← hprod]
  have hbij : Function.Bijective (fun z => chart.symm (g * chart z)) :=
    chart.symm.bijective.comp ((Group.mulLeft_bijective g).comp chart.bijective)
  rw [heq] at hbij ⊢
  apply map_eq_self_of_unit_jacobian μ _
    (fun y => (finiteDynkinDifferential coeff ![chart.symm g, y]
      (rightVariableDifferential (L := L))).toContinuousLinearMap)
    (fun y => hasFDerivAt_rightDynkin coeff (chart.symm g) y) hbij
  intro y
  exact rightDynkinDifferential_det coeff hunit hd (chart.symm g) y

end PolycyclicRecognition

end

end OAI
