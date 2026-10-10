import OAI.Geometry.NodalSets.Charts.TransformedDensity
import OAI.Geometry.NodalSets.Coefficients.CommonCoefficientExtension

namespace OAI

namespace Yau.Geometry
open scoped ContDiff
open Yau.Jets
noncomputable section
attribute [local instance] clmTopology clmAdd clmModule

def chartPrincipal (g : Coord → Coord →L[ℝ] Coord →L[ℝ] ℝ)
    (i j : Fin 4) (p : QuadParam Coord) (x : Coord) : ℝ :=
  (inversePulledForm g p x (ContinuousLinearMap.proj j)) i

def chartFlux (g : Coord → Coord →L[ℝ] Coord →L[ℝ] ℝ) (w : Coord → ℝ)
    (i j : Fin 4) (p : QuadParam Coord) (x : Coord) : ℝ :=
  chartDensity w p x * chartPrincipal g i j p x

def chartDrift (g : Coord → Coord →L[ℝ] Coord →L[ℝ] ℝ) (w : Coord → ℝ)
    (j : Fin 4) (p : QuadParam Coord) (x : Coord) : ℝ :=
  (chartDensity w p x)⁻¹ * ∑ i, fderiv ℝ (chartFlux g w i j p) x (Pi.single i 1)

lemma chartPrincipal_smooth_at (g : Coord → Coord →L[ℝ] Coord →L[ℝ] ℝ)
    (hg : ContDiff ℝ ∞ g) (p : QuadParam Coord) (x : Coord)
    (hp : ∀ v, v ≠ 0 → 0 < g (rawQuadratic p x) v v)
    (J : Coord ≃L[ℝ] Coord) (hJ : fderiv ℝ (rawQuadratic p) x = J.toContinuousLinearMap)
    (i j : Fin 4) : ContDiffAt ℝ ∞ (Function.uncurry (chartPrincipal g i j)) (p,x) := by
  have hpos := pulledForm_positive g p x hp J hJ
  exact (ContinuousLinearMap.proj i : Coord →L[ℝ] ℝ).contDiff.contDiffAt.comp (p,x)
    ((inversePulledForm_smooth_at g hg p x
      (positiveMetricEquiv (pulledForm g p x) hpos) rfl).clm_apply contDiffAt_const)

lemma chartDrift_smooth_at (g : Coord → Coord →L[ℝ] Coord →L[ℝ] ℝ)
    (hg : ContDiff ℝ ∞ g) (w : Coord → ℝ) (hw : ContDiff ℝ ∞ w)
    (p : QuadParam Coord) (x : Coord)
    (hp : ∀ v, v ≠ 0 → 0 < g (rawQuadratic p x) v v) (hwpos : 0 < w (rawQuadratic p x))
    (J : Coord ≃L[ℝ] Coord) (hJ : fderiv ℝ (rawQuadratic p) x = J.toContinuousLinearMap)
    (j : Fin 4) : ContDiffAt ℝ ∞ (Function.uncurry (chartDrift g w j)) (p,x) := by
  have hW := chartDensity_smooth_at w hw p x J hJ
  apply (hW.inv (ne_of_gt (chartDensity_pos w p x hwpos J hJ))).mul
  apply ContDiffAt.sum
  intro i _
  exact (smooth_spatial_fderiv_at (chartFlux g w i j) p x
    (hW.mul (chartPrincipal_smooth_at g hg p x hp J hJ i j))).clm_apply contDiffAt_const

variable {T : Type*} [TopologicalSpace T]

theorem actual_chart_coefficient_extensions
    (g : Coord → Coord →L[ℝ] Coord →L[ℝ] ℝ) (hg : ContDiff ℝ ∞ g)
    (w : Coord → ℝ) (hw : ContDiff ℝ ∞ w)
    (p : T → QuadParam Coord) (hp : Continuous p)
    (beta : Coord → ℝ) (hbeta : ContDiff ℝ ∞ beta)
    (hpos : ∀ t x, x ∈ tsupport beta → ∀ v, v ≠ 0 → 0 < g (rawQuadratic (p t) x) v v)
    (hwpos : ∀ t x, x ∈ tsupport beta → 0 < w (rawQuadratic (p t) x))
    (hJ : ∀ t x, x ∈ tsupport beta → ∃ J : Coord ≃L[ℝ] Coord,
      fderiv ℝ (rawQuadratic (p t)) x = J.toContinuousLinearMap) :
    (∀ t i j, ContDiff ℝ ∞ (cutoffCoefficient beta (chartPrincipal g i j) (p t))) ∧
    (∀ t j, ContDiff ℝ ∞ (cutoffCoefficient beta (chartDrift g w j) (p t))) ∧
    (∀ k i j, Continuous (fun z : T × Coord ↦ iteratedFDeriv ℝ k
      (cutoffCoefficient beta (chartPrincipal g i j) (p z.1)) z.2)) ∧
    ∀ k j, Continuous (fun z : T × Coord ↦ iteratedFDeriv ℝ k
      (cutoffCoefficient beta (chartDrift g w j) (p z.1)) z.2) := by
  have hG (i j : Fin 4) := common_cutoff_coefficient_family beta hbeta (chartPrincipal g i j) p hp
    (fun t x hx ↦ by
      obtain ⟨J,hJe⟩ := hJ t x hx
      exact chartPrincipal_smooth_at g hg (p t) x (hpos t x hx) J hJe i j)
  have hB (j : Fin 4) := common_cutoff_coefficient_family beta hbeta (chartDrift g w j) p hp
    (fun t x hx ↦ by
      obtain ⟨J,hJe⟩ := hJ t x hx
      exact chartDrift_smooth_at g hg w hw (p t) x (hpos t x hx) (hwpos t x hx) J hJe j)
  exact ⟨fun t i j ↦ (hG i j).1 t, fun t j ↦ (hB j).1 t,
    fun k i j ↦ (hG i j).2 k, fun k j ↦ (hB j).2 k⟩

end
end Yau.Geometry

end OAI
