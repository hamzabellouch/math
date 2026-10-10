import Mathlib
import OAI.Analysis.CoulombIonization.FormDomain.L2

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
open MeasureTheory Filter Complex TopologicalSpace
open scoped Topology InnerProductSpace ENNReal
open MeasureTheory Filter Complex
open scoped Topology BigOperators ComplexConjugate FourierTransform SchwartzMap ENNReal
open MeasureTheory Filter
open scoped Topology ContDiff SchwartzMap FourierTransform ENNReal
open MeasureTheory Filter
open scoped ContDiff InnerProductSpace Topology
namespace CoulombSobolev
open CoulombPauli
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
  {B : Type*} [MeasurableSpace B] {ν : Measure B} [SigmaFinite ν]

def HasWeakL2PartialDerivative
    (ψ u : Lp ℂ 2 ((volume : Measure V).prod ν)) (v : V) : Prop :=
  ∀ φ : Test V,
    (tensorLeft (φ.deriv v).toL2).adjoint ψ + (tensorLeft φ.toL2).adjoint u = 0

lemma projected_weak_derivative_general {ψ u : Lp ℂ 2 ((volume : Measure V).prod ν)}
    {v : V} (hw : HasWeakL2PartialDerivative ψ u v) (w : Lp ℂ 2 ν) :
    CoulombAtom.HasWeakDirectionalDerivative ((tensorRight w).adjoint ψ)
      ((tensorRight w).adjoint u) v := by
  intro φ hφ hcφ
  let Φ : Test V := ⟨φ,hφ,hcφ⟩
  have h : inner ℂ (Φ.deriv v).toL2 ((tensorRight w).adjoint ψ) +
      inner ℂ Φ.toL2 ((tensorRight w).adjoint u) = 0 := by
    rw [← tensor_adjoint_exchange, ← tensor_adjoint_exchange, ← inner_add_right,
      hw Φ, inner_zero_right]
  rw [Test.inner_toL2, Test.inner_toL2] at h
  apply eq_neg_of_add_eq_zero_left
  convert h using 1
  apply congrArg₂ (· + ·) _ rfl
  apply integral_congr_ae
  filter_upwards [] with x
  congr 2
  exact (hφ.differentiable (by simp) x).lineDeriv_eq_fderiv
end CoulombSobolev

end

end OAI
