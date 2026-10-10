import OAI.Geometry.SurfaceImmersion.Whitney.CompactFramedCurveTube

namespace OAI

/-! Actual smooth target coordinates straightening a regular curve germ. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)
local instance curveChartNormed : NormedAddCommGroup (Base × ℝ) := inferInstance
local instance curveChartSpace : NormedSpace ℝ (Base × ℝ) := inferInstance

theorem regular_curve_target_coordinates {c : ℝ → (Fin 3 → ℝ)}
    (hc : ContDiff ℝ ∞ c) (t : ℝ) (ht : deriv c t ≠ 0) :
    ∃ (e : OpenPartialHomeomorph (Base × ℝ) (Fin 3 → ℝ)) (U : Set ℝ),
      IsOpen U ∧ t ∈ U ∧ ContDiff ℝ ∞ e ∧ ContDiffOn ℝ ∞ e.symm e.target ∧
      ∀ s ∈ U, (0,s) ∈ e.source ∧ e (0,s) = c s := by
  obtain ⟨a,ha⟩ := exists_curve_transverse_vector (deriv c) (contDiff_infty_iff_deriv.mp hc).2
  let T := framedCurveTube c a
  have hT : ContDiff ℝ ∞ T := framedCurveTube_smooth hc a
  have hD := framedCurveTube_regular_axis hc ha t ht
  let R : (Base × ℝ) ≃L[ℝ] (Fin 3 → ℝ) :=
    ContinuousLinearEquiv.ofBijective (fderiv ℝ T (0,t))
      (LinearMap.ker_eq_bot.mpr hD.1) (LinearMap.range_eq_top.mpr hD.2)
  have hd : HasFDerivAt T R.toContinuousLinearMap (0,t) :=
    (hT.differentiable (by simp) (0,t)).hasFDerivAt
  let e₀ := hT.contDiffAt.toOpenPartialHomeomorph T hd (by simp)
  let W : Set (Base × ℝ) := {z | IsUnit (R.symm.toContinuousLinearMap.comp (fderiv ℝ T z))}
  have hcont : Continuous (fun z => R.symm.toContinuousLinearMap.comp (fderiv ℝ T z)) :=
    continuous_const.clm_comp (hT.continuous_fderiv (by simp))
  have hW : IsOpen W := Units.isOpen.preimage hcont
  have htW : (0,t) ∈ W := by
    apply ContinuousLinearMap.isUnit_iff_bijective.mpr
    exact R.symm.bijective.comp hD
  let e := e₀.restrOpen W hW
  have he : (e : Base × ℝ → (Fin 3 → ℝ)) = T := rfl
  have htE : (0,t) ∈ e.source :=
    ⟨hT.contDiffAt.mem_toOpenPartialHomeomorph_source hd (by simp),htW⟩
  let U : Set ℝ := (fun s => ((0 : Base),s)) ⁻¹' e.source
  have hU : IsOpen U := e.open_source.preimage (continuous_const.prodMk continuous_id)
  refine ⟨e,U,hU,htE,by simpa only [he] using hT,?_,?_⟩
  · intro y hy
    obtain ⟨u,hu⟩ := (e.map_target hy).2
    let D := (ContinuousLinearEquiv.ofUnit u).trans R
    have hde : D.toContinuousLinearMap = fderiv ℝ T (e.symm y) := by
      apply ContinuousLinearMap.ext
      intro v
      change R ((u : (Base × ℝ) →L[ℝ] (Base × ℝ)) v) = _
      rw [hu]
      exact R.apply_symm_apply _
    have hdy : HasFDerivAt e D.toContinuousLinearMap (e.symm y) := by
      rw [he,hde]
      exact (hT.differentiable (by simp) _).hasFDerivAt
    exact (e.contDiffAt_symm hy hdy (by rw [he]; exact hT.contDiffAt)).contDiffWithinAt
  · intro s hs
    refine ⟨hs,?_⟩
    change framedCurveTube c a (0,s) = c s
    simp [framedCurveTube]

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
