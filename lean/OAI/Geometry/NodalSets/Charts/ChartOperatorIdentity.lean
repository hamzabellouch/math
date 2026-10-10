import OAI.Geometry.NodalSets.Coefficients.ComplexChartCoefficient
import OAI.Geometry.NodalSets.Elliptic.WeightedCoordinateOperator

namespace OAI

namespace Yau.Geometry
open scoped ContDiff
open Yau.Jets
noncomputable section
attribute [local instance] clmTopology clmAdd clmModule

lemma inverse_form_pair (G : Coord →L[ℝ] Coord →L[ℝ] ℝ)
    (hp : ∀ v, v ≠ 0 → 0 < G v v) (a : Coord →L[ℝ] ℝ) (v : Coord) :
    G (ContinuousLinearMap.inverse G a) v = a v := by
  have hi : ContinuousLinearMap.inverse G = (positiveMetricEquiv G hp).symm.toContinuousLinearMap :=
    ContinuousLinearMap.inverse_equiv (positiveMetricEquiv G hp)
  change positiveMetricEquiv G hp (ContinuousLinearMap.inverse G a) v = _
  rw [hi, ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.apply_symm_apply]

lemma chartPrincipal_symmetric (g : Coord → Coord →L[ℝ] Coord →L[ℝ] ℝ)
    (hs : ∀ x u v, g x u v = g x v u) (p : QuadParam Coord) (x : Coord)
    (hp : ∀ v, v ≠ 0 → 0 < g (rawQuadratic p x) v v)
    (J : Coord ≃L[ℝ] Coord) (hJ : fderiv ℝ (rawQuadratic p) x = J.toContinuousLinearMap)
    (i j : Fin 4) : chartPrincipal g i j p x = chartPrincipal g j i p x := by
  have hpos := pulledForm_positive g p x hp J hJ
  have hsym (u v : Coord) : pulledForm g p x u v = pulledForm g p x v u := hs _ _ _
  have h := hsym (inversePulledForm g p x (ContinuousLinearMap.proj i))
    (inversePulledForm g p x (ContinuousLinearMap.proj j))
  change pulledForm g p x (ContinuousLinearMap.inverse (pulledForm g p x) (ContinuousLinearMap.proj i))
      (ContinuousLinearMap.inverse (pulledForm g p x) (ContinuousLinearMap.proj j)) = _ at h
  simp only [inversePulledForm] at h
  rw [inverse_form_pair _ hpos, inverse_form_pair _ hpos] at h
  exact h

lemma coordPartial_ofReal_at (f : Coord → ℝ) (x : Coord) (hf : DifferentiableAt ℝ f x) (i : Fin 4) :
    coordPartial i (fun z ↦ (f z : ℂ)) x = (fderiv ℝ f x (Pi.single i 1) : ℂ) := by
  change fderiv ℝ (Complex.ofRealCLM ∘ f) x (Pi.single i 1) = _
  rw [(Complex.ofRealCLM.hasFDerivAt.comp x hf.hasFDerivAt).fderiv]
  rfl

lemma densityDrift_chart (g : Coord → Coord →L[ℝ] Coord →L[ℝ] ℝ) (w : Coord → ℝ)
    (p : QuadParam Coord) (x : Coord)
    (hF : ∀ i j, DifferentiableAt ℝ (chartFlux g w i j p) x) (j : Fin 4) :
    densityDrift (fun z ↦ (chartDensity w p z : ℂ))
      (fun i j ↦ complexPrincipal g i j p) j x = complexDrift g w j p x := by
  have he (i j : Fin 4) : (fun z ↦ (chartDensity w p z : ℂ) * complexPrincipal g i j p z) =
      fun z ↦ (chartFlux g w i j p z : ℂ) := by
    funext z
    simp [chartFlux,complexPrincipal,Complex.ofReal_mul]
  unfold densityDrift
  simp_rw [he,coordPartial_ofReal_at _ x (hF _ _)]
  simp [complexDrift,chartDrift,Complex.ofReal_mul,Complex.ofReal_inv,Complex.ofReal_sum]

theorem actual_chart_weighted_operator
    (g : Coord → Coord →L[ℝ] Coord →L[ℝ] ℝ) (hg : ContDiff ℝ ∞ g)
    (w : Coord → ℝ) (hw : ContDiff ℝ ∞ w) (p : QuadParam Coord) (x : Coord)
    (hp : ∀ v, v ≠ 0 → 0 < g (rawQuadratic p x) v v) (hwpos : 0 < w (rawQuadratic p x))
    (J : Coord ≃L[ℝ] Coord) (hJ : fderiv ℝ (rawQuadratic p) x = J.toContinuousLinearMap)
    (u : Coord → ℂ) (hu : ContDiff ℝ ∞ u) :
    weightedCoordinateOperator (fun z ↦ (chartDensity w p z : ℂ))
      (fun i j ↦ complexPrincipal g i j p) u x =
      smoothSecondOrder (fun i j ↦ complexPrincipal g i j p) (fun j ↦ complexDrift g w j p) u x := by
  have hF (i j : Fin 4) : DifferentiableAt ℝ (chartFlux g w i j p) x := by
    have h := ((chartDensity_smooth_at w hw p x J hJ).mul
      (chartPrincipal_smooth_at g hg p x hp J hJ i j)).comp x
        (contDiffAt_const.prodMk contDiffAt_id)
    exact h.differentiableAt (by simp)
  have hFc (i j : Fin 4) : DifferentiableAt ℝ
      (fun z ↦ (chartDensity w p z : ℂ) * complexPrincipal g i j p z) x := by
    have he : (fun z ↦ (chartDensity w p z : ℂ) * complexPrincipal g i j p z) =
        Complex.ofRealCLM ∘ chartFlux g w i j p := by
      funext z
      simp [chartFlux,complexPrincipal]
    rw [he]
    exact Complex.ofRealCLM.differentiableAt.comp x (hF i j)
  rw [weightedCoordinateOperator_eq _ _ _ x
    (Complex.ofReal_ne_zero.mpr (ne_of_gt (chartDensity_pos w p x hwpos J hJ))) hFc
    (fun j ↦ (coordPartial_contDiff hu j).differentiable (by simp) x)]
  unfold smoothSecondOrder
  simp_rw [densityDrift_chart g w p x hF]

end
end Yau.Geometry

end OAI
