import OAI.Analysis.CircleDomains.Topology.CircleChainRule
import OAI.Analysis.CircleDomains.Sobolev.MetricChartEnergy

namespace OAI

/-!
# The finite real chart of a metric-conformal sphere map

This identifies the actual real derivative matrix of the finite-chart
map with the complex chart derivative used in metric conformality.
-/

open Set Filter Matrix
open scoped Topology

noncomputable section

namespace CircleDomainRigidity

open FiniteTransfer

def sphereRealMap (f : Sphere → Sphere) (x : ℝ × ℝ) : ℝ × ℝ :=
  Complex.equivRealProdCLM (finiteCoord (f ((Complex.equivRealProdCLM.symm x : ℂ) : Sphere)))

def complexToRealDerivative (A : ℂ →L[ℝ] ℂ) : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) :=
  Complex.equivRealProdCLM.toContinuousLinearMap.comp
    (A.comp Complex.equivRealProdCLM.symm.toContinuousLinearMap)

theorem planeMatrix_complexToRealDerivative (A : ℂ →L[ℝ] ℂ) :
    planeDerivativeMatrix (complexToRealDerivative A) = complexRealMatrix A := by
  rw [planeDerivativeMatrix_eq_columns]
  rfl

theorem sphereRealMap_hasFDerivAt
    {g : (ℝ × ℝ) → PlanarMetric} {f : Sphere → Sphere} {x : ℝ × ℝ}
    (hf : IsMetricConformalAt g f ((Complex.equivRealProdCLM.symm x : ℂ) : Sphere))
    (hfinite : f ((Complex.equivRealProdCLM.symm x : ℂ) : Sphere) ≠ OnePoint.infty) :
    HasFDerivAt (sphereRealMap f)
      (complexToRealDerivative (fderiv ℝ
        (sphereLocalMap f ((Complex.equivRealProdCLM.symm x : ℂ) : Sphere))
        (Complex.equivRealProdCLM.symm x))) x := by
  let p : Sphere := ((Complex.equivRealProdCLM.symm x : ℂ) : Sphere)
  have hd : HasFDerivAt (sphereLocalMap f p)
      (fderiv ℝ (sphereLocalMap f p) (Complex.equivRealProdCLM.symm x))
      (Complex.equivRealProdCLM.symm x) := by
    simpa only [p, chart, OnePoint.coe_ne_infty, ite_false, finiteCoord,
      OnePoint.elim_some, id_eq] using hf.2.1.hasFDerivAt
  have hc := Complex.equivRealProdCLM.hasFDerivAt.comp x
    (hd.comp x Complex.equivRealProdCLM.symm.hasFDerivAt)
  have heq : sphereRealMap f =
      Complex.equivRealProdCLM ∘ sphereLocalMap f p ∘ Complex.equivRealProdCLM.symm := by
    funext y
    simp only [sphereRealMap, sphereLocalMap, p, chart, chartSymm,
      OnePoint.coe_ne_infty, ite_false, hfinite, Function.comp_apply]
  simpa only [heq, complexToRealDerivative] using hc

theorem metric_conformal_real_chart
    {g : (ℝ × ℝ) → PlanarMetric} {f : Sphere → Sphere} {x : ℝ × ℝ}
    (hf : IsMetricConformalAt g f ((Complex.equivRealProdCLM.symm x : ℂ) : Sphere))
    (hg : (g x).PosDef)
    (hfinite : f ((Complex.equivRealProdCLM.symm x : ℂ) : Sphere) ≠ OnePoint.infty) :
    DifferentiableAt ℝ (sphereRealMap f) x ∧
      0 < (fderiv ℝ (sphereRealMap f) x).det ∧
      ∃ c : ℝ, 0 < c ∧ g x = c •
        ((planeDerivativeMatrix (fderiv ℝ (sphereRealMap f) x))ᵀ *
          planeDerivativeMatrix (fderiv ℝ (sphereRealMap f) x)) := by
  let p : Sphere := ((Complex.equivRealProdCLM.symm x : ℂ) : Sphere)
  have hmetric : sphereChartMetric g p = g x := by
    simp only [p, sphereChartMetric, OnePoint.coe_ne_infty, ite_false, finiteCoord,
      OnePoint.elim_some, id_eq, ContinuousLinearEquiv.apply_symm_apply]
  have hcenter : chart p p = Complex.equivRealProdCLM.symm x := by
    simp only [p, chart, OnePoint.coe_ne_infty, ite_false, finiteCoord, OnePoint.elim_some, id_eq]
  have hd := sphereRealMap_hasFDerivAt hf hfinite
  have hmat : planeDerivativeMatrix (fderiv ℝ (sphereRealMap f) x) =
      complexRealMatrix (fderiv ℝ (sphereLocalMap f p) (chart p p)) := by
    rw [hd.fderiv, planeMatrix_complexToRealDerivative, hcenter]
  refine ⟨hd.differentiableAt, ?_, ?_⟩
  · rw [← det_planeDerivativeMatrix, hmat, det_complexRealMatrix]
    exact hf.2.2.choose_spec.2.2.2.2
  · have hsym : (sphereChartMetric g p).IsSymm := by
      rw [hmetric]
      exact hg.isHermitian.isSymm
    obtain ⟨c, hc, heq⟩ := metric_eq_scaled_chart_gram hf hsym
    change sphereChartMetric g p = _ at heq
    rw [hmetric] at heq
    refine ⟨c, hc, ?_⟩
    rw [hmat]
    exact heq

theorem sphereRealMap_injOn
    {f : Sphere → Sphere} {U : Set Sphere} (hf : InjOn f U)
    {s : Set (ℝ × ℝ)}
    (hs : ∀ x ∈ s, ((Complex.equivRealProdCLM.symm x : ℂ) : Sphere) ∈ U)
    (hfinite : ∀ x ∈ s, f ((Complex.equivRealProdCLM.symm x : ℂ) : Sphere) ≠ OnePoint.infty) :
    InjOn (sphereRealMap f) s := by
  intro x hx y hy hxy
  have hcoord := Complex.equivRealProdCLM.injective hxy
  have hvalues : f ((Complex.equivRealProdCLM.symm x : ℂ) : Sphere) =
      f ((Complex.equivRealProdCLM.symm y : ℂ) : Sphere) := by
    have hc := congrArg ((↑) : ℂ → Sphere) hcoord
    exact (CannonMobius.coe_coordinate (hfinite x hx)).symm.trans
      (hc.trans (CannonMobius.coe_coordinate (hfinite y hy)))
  exact Complex.equivRealProdCLM.symm.injective
    (OnePoint.coe_injective (hf (hs x hx) (hs y hy) hvalues))

end CircleDomainRigidity

end

end OAI
