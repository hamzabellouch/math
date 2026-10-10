import OAI.Geometry.NodalSets.Charts.ComplexMetricFlux

namespace OAI

namespace Yau.Geometry
open Yau.Jets Filter
open scoped ContDiff Topology
noncomputable section
attribute [local instance] clmTopology clmAdd clmModule

def sourceWeightedOperator (g : Coord → Coord →L[ℝ] Coord →L[ℝ] ℝ)
    (w : Coord → ℝ) (u : Coord → ℂ) (x : Coord) : ℂ :=
  (w x : ℂ)⁻¹ * complexDivergence (sourceFlux g w u) x

lemma weightedCoordinateOperator_divergence (W : Coord → ℂ)
    (a : Fin 4 → Fin 4 → Coord → ℂ) (u : Coord → ℂ) (x : Coord)
    (hflux : ∀ i j, DifferentiableAt ℝ (fun z ↦ W z * a i j z) x)
    (hu : ∀ j, DifferentiableAt ℝ (coordPartial j u) x) :
    weightedCoordinateOperator W a u x = (W x)⁻¹ *
      complexDivergence (fun i z ↦ ∑ j, (W z * a i j z) * coordPartial j u z) x := by
  unfold weightedCoordinateOperator complexDivergence
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  exact (coordPartial_sum_at _ x (fun j ↦ (hflux i j).mul (hu j)) i).symm

theorem actual_weighted_coordinate_invariance
    (g : Coord → Coord →L[ℝ] Coord →L[ℝ] ℝ) (hg : ContDiff ℝ ∞ g)
    (hp : ∀ x v, v ≠ 0 → 0 < g x v v)
    (w : Coord → ℝ) (hw : ContDiff ℝ ∞ w) (p : QuadParam Coord) (x : Coord)
    (hwpos : 0 < w (rawQuadratic p x))
    (J : Coord ≃L[ℝ] Coord) (hJ : fderiv ℝ (rawQuadratic p) x = J.toContinuousLinearMap)
    (u : Coord → ℂ) (hu : ContDiff ℝ ∞ u) :
    smoothSecondOrder (fun i j ↦ complexPrincipal g i j p)
      (fun j ↦ complexDrift g w j p) (u ∘ rawQuadratic p) x =
        sourceWeightedOperator g w u (rawQuadratic p x) := by
  have hF : ContDiff ℝ ∞ (rawQuadratic p) :=
    rawQuadratic_smooth.comp (contDiff_const.prodMk contDiff_id)
  have huc := hu.comp hF
  have hJe : ∀ᶠ z in 𝓝 x, ∃ Jz : Coord ≃L[ℝ] Coord,
      Jz.toContinuousLinearMap = fderiv ℝ (rawQuadratic p) z :=
    (hF.fderiv_right (m := ∞) (by simp)).continuous.continuousAt.eventually
      (ContinuousLinearEquiv.isOpen.mem_nhds ⟨J,hJ.symm⟩)
  have he (i : Fin 4) : pulledFlux g w p (u ∘ rawQuadratic p) i =ᶠ[𝓝 x]
      absolutePiola (rawQuadratic p) (sourceFlux g w u) i := by
    filter_upwards [hJe] with z hz
    obtain ⟨Jz,hJz⟩ := hz
    exact actual_pulled_flux g w p z (hp _) Jz hJz.symm u
      (hu.differentiable (by simp) _) i
  have hdiv : complexDivergence (pulledFlux g w p (u ∘ rawQuadratic p)) x =
      complexDivergence (absolutePiola (rawQuadratic p) (sourceFlux g w u)) x := by
    apply Finset.sum_congr rfl
    intro i _
    exact congrArg (fun L : Coord →L[ℝ] ℂ ↦ L (Pi.single i 1)) (he i).fderiv_eq
  have hflux (i j : Fin 4) : DifferentiableAt ℝ
      (fun z ↦ (chartDensity w p z : ℂ) * complexPrincipal g i j p z) x := by
    have hW := ((chartDensity_smooth_at w hw p x J hJ).comp x
      (contDiffAt_const.prodMk contDiffAt_id))
    have ha := ((chartPrincipal_smooth_at g hg p x (hp _) J hJ i j).comp x
      (contDiffAt_const.prodMk contDiffAt_id))
    exact ((Complex.ofRealCLM.contDiff.contDiffAt.comp x hW).mul
      (Complex.ofRealCLM.contDiff.contDiffAt.comp x ha)).differentiableAt (by simp)
  rw [← actual_chart_weighted_operator g hg w hw p x (hp _) hwpos J hJ
    (u ∘ rawQuadratic p) huc]
  rw [weightedCoordinateOperator_divergence _ _ _ x hflux
    (fun j ↦ (coordPartial_contDiff huc j).differentiable (by simp) x)]
  change (chartDensity w p x : ℂ)⁻¹ *
    complexDivergence (pulledFlux g w p (u ∘ rawQuadratic p)) x = _
  rw [hdiv, absolutePiola_divergence (rawQuadratic p) hF (sourceFlux g w u) x
    (fun a ↦ (sourceFlux_smooth_at g hg w hw u hu _ (hp _) a).differentiableAt (by simp))
    (by change coordDet (fderiv ℝ (rawQuadratic p) x) ≠ 0
        rw [hJ]; exact coordDet_equiv_ne_zero J)]
  have hd : (|(jacobian (rawQuadratic p) x).det| : ℝ) ≠ 0 := by
    apply abs_ne_zero.mpr
    change coordDet (fderiv ℝ (rawQuadratic p) x) ≠ 0
    rw [hJ]; exact coordDet_equiv_ne_zero J
  unfold sourceWeightedOperator chartDensity
  change ((w (rawQuadratic p x) * |(jacobian (rawQuadratic p) x).det| : ℝ) : ℂ)⁻¹ * _ = _
  have hdC := Complex.ofReal_ne_zero.mpr hd
  have hwC := Complex.ofReal_ne_zero.mpr (ne_of_gt hwpos)
  push_cast
  field_simp

end
end Yau.Geometry

end OAI
