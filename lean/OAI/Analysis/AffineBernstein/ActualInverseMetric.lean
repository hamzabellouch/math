import Mathlib
import OAI.Analysis.AffineBernstein.JetCalculus
import OAI.Analysis.AffineBernstein.ParametricInverseMetric

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

open Filter
open scoped Topology

def graphConormalAt {n : ℕ} (u : Space n → ℝ) (x : Space n) :
    (Space n × ℝ) →L[ℝ] ℝ :=
  (ContinuousLinearMap.snd ℝ (Space n) ℝ) -
    (fderiv ℝ u x).comp (ContinuousLinearMap.fst ℝ (Space n) ℝ)

lemma graphConormalAt_null {n : ℕ} {u : Space n → ℝ} {x : Space n}
    (hu : DifferentiableAt ℝ u x) :
    (graphConormalAt u x).comp (fderiv ℝ (fun y => (y,u y)) x) = 0 := by
  ext v
  simp [graphMap_fderiv hu,graphConormalAt]

lemma parametricSecondForm_graph {n : ℕ} {u : Space n → ℝ} {x : Space n}
    (hu : ContDiffAt ℝ ∞ u x) (ν : (Space n × ℝ) →L[ℝ] ℝ) :
    parametricSecondForm (fun y => (y,u y)) ν x = ν ((0:Space n),1) • hessian u x := by
  ext i j
  change dirDeriv (coordinateVector n i) (dirDeriv (coordinateVector n j)
    (fun y => ν (y,u y))) x = ν ((0:Space n),1) * hessian u x i j
  rw [dirDeriv_eq_second (f := fun y => ν (y,u y))
    (ν.contDiff.contDiffAt.comp x (contDiffAt_id.prodMk hu)),
    second_fderiv_clm_comp ν (Y := fun y => (y,u y))
      (contDiffAt_id.prodMk hu),graphMap_second hu]
  have hv (t : ℝ) : ((0:Space n),t) = t • ((0:Space n),1) := by simp
  rw [hv,map_smul,smul_eq_mul]
  rw [show fderiv ℝ (fderiv ℝ u) x (coordinateVector n i) (coordinateVector n j) =
    hessian u x i j from (dirDeriv_eq_second hu _ _).symm]
  ring

lemma parametricInverseMetric_graph {n : ℕ} {u f : Space n → ℝ} {x : Space n}
    (hu : ContDiffAt ℝ ∞ u x) (ν : (Space n × ℝ) →L[ℝ] ℝ)
    (hH : (hessian u x).det ≠ 0) (hc : ν ((0:Space n),1) ≠ 0) :
    parametricInverseMetric (fun y => (y,u y)) ν f x =
      (ν ((0:Space n),1))⁻¹ * inverseMatrixPair (hessian u x)
        (fun i => dirDeriv (coordinateVector n i) f x)
        (fun i => dirDeriv (coordinateVector n i) f x) := by
  unfold parametricInverseMetric
  rw [parametricSecondForm_graph hu ν]
  exact inverseMatrixPair_smul_matrix _ hH _ hc _ _

/- Pointwise norm transport in an arbitrary smooth graph chart. The factor
is the norm of the ACTUAL conormal, not its vertical component. -/
theorem graph_chart_inverseMetric_transport {n : ℕ} {u f : Space n → ℝ}
    {φ : Space n → Space n} {x : Space n}
    (hu : ContDiffAt ℝ ∞ u (φ x)) (hφ : ContDiffAt ℝ ∞ φ x)
    (hH : (hessian u (φ x)).det ≠ 0) (hJ : (parametricJacobian φ x).det ≠ 0)
    (hf : DifferentiableAt ℝ f (φ x))
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (L : E ≃L[ℝ] (Space n × ℝ)) (a : Space n × ℝ)
    {X : Space n → E} (he : (fun y => a+L (X y)) =ᶠ[nhds x] (fun y => (φ y,u (φ y))))
    (c : ℝ) (hc : 0 < c) :
    let ζ := (graphConormalAt u (φ x)).comp L.toContinuousLinearMap
    ‖c • ζ‖ * parametricInverseMetric X (c • ζ) (f ∘ φ) x =
      ‖ζ‖ * inverseMatrixPair (hessian u (φ x))
        (fun i => dirDeriv (coordinateVector n i) f (φ x))
        (fun i => dirDeriv (coordinateVector n i) f (φ x)) := by
  let ζ := (graphConormalAt u (φ x)).comp L.toContinuousLinearMap
  let ν := c • graphConormalAt u (φ x)
  have hν : ν.comp (fderiv ℝ (fun y => (y,u y)) (φ x)) = 0 := by
    ext v
    have hh := congrArg (fun T : Space n →L[ℝ] ℝ => T v)
      (graphConormalAt_null (hu.differentiableAt (by simp)))
    simpa [ν] using congrArg (fun t : ℝ => c*t) hh
  have hsecond : parametricSecondForm X (c • ζ) x =
      parametricSecondForm (fun y => (φ y,u (φ y))) ν x := by
    have hq : (fun y => (c • ζ) (X y)) =ᶠ[nhds x]
        (fun y => ν (φ y,u (φ y))-ν a) := he.mono (fun y hy => by
      have hh := congrArg ν hy
      have hh' : ν (L (X y)) = ν (φ y,u (φ y))-ν a := by
        rw [map_add] at hh
        linarith
      simpa [ν,ζ] using hh')
    change hessian _ x = hessian _ x
    rw [hessian_eq_of_eventuallyEq hq]
    have hh : (fun y => ν (φ y,u (φ y))-ν a) = (fun y => ν (φ y,u (φ y))+(-ν a)) := by
      funext y; ring
    rw [hh,hessian_add_constant]
  have hmetric : parametricInverseMetric X (c • ζ) (f ∘ φ) x =
      c⁻¹ * inverseMatrixPair (hessian u (φ x))
        (fun i => dirDeriv (coordinateVector n i) f (φ x))
        (fun i => dirDeriv (coordinateVector n i) f (φ x)) := by
    unfold parametricInverseMetric
    rw [hsecond]
    change parametricInverseMetric ((fun y => (y,u y)) ∘ φ) ν (f ∘ φ) x = _
    rw [parametricInverseMetric_comp (X := fun y => (y,u y)) (contDiffAt_id.prodMk hu) hφ hf ν hν hJ,
      parametricInverseMetric_graph hu ν hH (by simpa [ν,graphConormalAt] using hc.ne')]
    simp [ν,graphConormalAt]
  change ‖c • ζ‖ * parametricInverseMetric X (c • ζ) (f ∘ φ) x = _
  rw [hmetric,norm_smul,Real.norm_eq_abs,abs_of_pos hc]
  field_simp
  simp [ζ,mul_comm]

end AffineBernstein
end

end OAI
