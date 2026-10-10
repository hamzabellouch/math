import OAI.Geometry.NodalSets.Charts.InverseMetricJet
import OAI.Geometry.NodalSets.Charts.NormalTaylorMetric
import OAI.Geometry.NodalSets.Elliptic.TransformedDrift

namespace OAI

namespace Yau.Geometry
open Filter
open scoped ContDiff Topology
open Yau.Jets
noncomputable section
attribute [local instance] clmTopology clmAdd clmModule

def complexPrincipal (g : Coord → Coord →L[ℝ] Coord →L[ℝ] ℝ)
    (i j : Fin 4) (p : QuadParam Coord) (x : Coord) : ℂ := chartPrincipal g i j p x

def complexDrift (g : Coord → Coord →L[ℝ] Coord →L[ℝ] ℝ) (w : Coord → ℝ)
    (j : Fin 4) (p : QuadParam Coord) (x : Coord) : ℂ := chartDrift g w j p x

variable {T : Type*} [TopologicalSpace T]

theorem complex_chart_coefficient_extensions
    (g : Coord → Coord →L[ℝ] Coord →L[ℝ] ℝ) (hg : ContDiff ℝ ∞ g)
    (w : Coord → ℝ) (hw : ContDiff ℝ ∞ w)
    (p : T → QuadParam Coord) (hp : Continuous p)
    (beta : Coord → ℝ) (hbeta : ContDiff ℝ ∞ beta)
    (hpos : ∀ t x, x ∈ tsupport beta → ∀ v, v ≠ 0 → 0 < g (rawQuadratic (p t) x) v v)
    (hwpos : ∀ t x, x ∈ tsupport beta → 0 < w (rawQuadratic (p t) x))
    (hJ : ∀ t x, x ∈ tsupport beta → ∃ J : Coord ≃L[ℝ] Coord,
      fderiv ℝ (rawQuadratic (p t)) x = J.toContinuousLinearMap) :
    (∀ t i j, ContDiff ℝ ∞ (cutoffCoefficient beta (complexPrincipal g i j) (p t))) ∧
    (∀ t j, ContDiff ℝ ∞ (cutoffCoefficient beta (complexDrift g w j) (p t))) ∧
    (∀ k i j, Continuous (fun z : T × Coord ↦ iteratedFDeriv ℝ k
      (cutoffCoefficient beta (complexPrincipal g i j) (p z.1)) z.2)) ∧
    ∀ k j, Continuous (fun z : T × Coord ↦ iteratedFDeriv ℝ k
      (cutoffCoefficient beta (complexDrift g w j) (p z.1)) z.2) := by
  have hG (i j : Fin 4) := common_cutoff_coefficient_family beta hbeta (complexPrincipal g i j) p hp
    (fun t x hx ↦ by
      obtain ⟨J,hJe⟩ := hJ t x hx
      exact Complex.ofRealCLM.contDiff.contDiffAt.comp (p t,x)
        (chartPrincipal_smooth_at g hg (p t) x (hpos t x hx) J hJe i j))
  have hB (j : Fin 4) := common_cutoff_coefficient_family beta hbeta (complexDrift g w j) p hp
    (fun t x hx ↦ by
      obtain ⟨J,hJe⟩ := hJ t x hx
      exact Complex.ofRealCLM.contDiff.contDiffAt.comp (p t,x)
        (chartDrift_smooth_at g hg w hw (p t) x (hpos t x hx) (hwpos t x hx) J hJe j))
  exact ⟨fun t i j ↦ (hG i j).1 t, fun t j ↦ (hB j).1 t,
    fun k i j ↦ (hG i j).2 k, fun k j ↦ (hB j).2 k⟩

theorem extended_actual_metric_normal_jets
    (g : Coord → Coord →L[ℝ] Coord →L[ℝ] ℝ) (hg : ContDiff ℝ ∞ g)
    (hs : ∀ x u v, g x u v = g x v u) (hp : ∀ x v, v ≠ 0 → 0 < g x v v)
    (y : Coord) (e : Coord ≃L[ℝ] Coord)
    (he : ∀ i j, g y (e (Pi.single i 1)) (e (Pi.single j 1)) = if i=j then 1 else 0)
    (beta : Coord → ℝ) (hb : beta =ᶠ[𝓝 0] fun _ ↦ 1) :
    let p := (y,e.toContinuousLinearMap,actualFrameConnection g y e)
    (∀ i j, cutoffCoefficient beta (complexPrincipal g i j) p 0 = if i=j then 1 else 0) ∧
    ∀ i j, fderiv ℝ (cutoffCoefficient beta (complexPrincipal g i j) p) 0 = 0 := by
  dsimp only
  have hj := actual_inverse_metric_normal_jets g hg hs hp y e he
  constructor
  · intro i j
    rw [(cutoffCoefficient_germ beta (complexPrincipal g i j) _ 0 hb).self_of_nhds]
    change (inverseChartCoeff g y e i j 0 : ℂ) = _
    rw [hj.1 i j]
    split_ifs <;> simp
  · intro i j
    rw [(cutoffCoefficient_germ beta (complexPrincipal g i j) _ 0 hb).fderiv_eq]
    let p : QuadParam Coord := (y,e.toContinuousLinearMap,actualFrameConnection g y e)
    have hreal : ContDiffAt ℝ ∞ (inverseChartCoeff g y e i j) 0 := by
      have hJ : fderiv ℝ (rawQuadratic p) 0 = e.toContinuousLinearMap :=
        (quadraticChartMap_deriv_zero y e _).fderiv
      exact (chartPrincipal_smooth_at g hg p 0
        (by simpa [p, rawQuadratic] using hp y) e hJ i j).comp 0
        (contDiffAt_const.prodMk contDiffAt_id)
    change fderiv ℝ (Complex.ofRealCLM ∘ inverseChartCoeff g y e i j) 0 = 0
    rw [(Complex.ofRealCLM.hasFDerivAt.comp 0 (hreal.differentiableAt (by simp)).hasFDerivAt).fderiv,
      hj.2 i j, ContinuousLinearMap.comp_zero]

theorem parametric_taylor_family (f : T → Coord → ℂ)
    (hc : ∀ k, Continuous (fun z : T × Coord ↦ iteratedFDeriv ℝ k (f z.1) z.2)) (m : ℕ) :
    ContinuousPolyFamily (fun t ↦ taylorPolynomial (f t) 0 m) := by
  unfold taylorPolynomial
  apply ContinuousPolyFamily.sum
  intro k _
  exact (ContinuousPolyFamily.const _).mul (tensorPolynomial_family _
    ((hc k).comp (continuous_id.prodMk continuous_const)))

end
end Yau.Geometry

end OAI
