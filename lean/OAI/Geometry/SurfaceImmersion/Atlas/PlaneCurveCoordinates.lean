import OAI.Geometry.SurfaceImmersion.Geometry.PlaneCurveFrame
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff

namespace OAI

/-! Actual local coordinates straightening a regular curve in the surface plane. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

def planeCurveTube (c : ℝ → Base) (v : Base) (x : Base) : Base := c (x 1)+x 0 • v

lemma planeCurveTube_smooth {c : ℝ → Base} (hc : ContDiff ℝ ∞ c) (v : Base) :
    ContDiff ℝ ∞ (planeCurveTube c v) :=
  (hc.comp (contDiff_apply ℝ ℝ 1)).add ((contDiff_apply ℝ ℝ 0).smul contDiff_const)

lemma planeCurveTube_fderiv {c : ℝ → Base} (hc : ContDiff ℝ ∞ c) (v : Base) (t : ℝ) :
    fderiv ℝ (planeCurveTube c v) ![0,t] = planeCurveLinear v (deriv c t) := by
  have hC := ((hc.differentiable (by simp) t).hasFDerivAt).comp ![0,t]
    (hasFDerivAt_apply (𝕜 := ℝ) (1 : Fin 2) ![0,t])
  have hV := (hasFDerivAt_apply (𝕜 := ℝ) (0 : Fin 2) ![0,t]).smul_const v
  have hd := hC.add hV
  change HasFDerivAt (planeCurveTube c v) _ ![0,t] at hd
  rw [hd.fderiv]
  apply ContinuousLinearMap.ext
  intro x
  simp [planeCurveLinear_apply,fderiv_eq_smul_deriv,add_comm]

theorem plane_curve_coordinates {c : ℝ → Base} (hc : ContDiff ℝ ∞ c)
    (t : ℝ) (ht : deriv c t ≠ 0) :
    ∃ (e : OpenPartialHomeomorph Base Base) (U : Set ℝ),
      IsOpen U ∧ t ∈ U ∧ ContDiff ℝ ∞ e ∧ ContDiffOn ℝ ∞ e.symm e.target ∧
      ∀ s ∈ U, (![0,s] : Base) ∈ e.source ∧ e ![0,s] = c s := by
  obtain ⟨v,hbij⟩ := exists_plane_curve_frame ht
  let T := planeCurveTube c v
  have hT : ContDiff ℝ ∞ T := planeCurveTube_smooth hc v
  have hD : Function.Bijective (fderiv ℝ T ![0,t]) := by
    rw [planeCurveTube_fderiv hc]
    exact hbij
  let R : Base ≃L[ℝ] Base := ContinuousLinearEquiv.ofBijective (fderiv ℝ T ![0,t])
    (LinearMap.ker_eq_bot.mpr hD.1) (LinearMap.range_eq_top.mpr hD.2)
  have hd : HasFDerivAt T R.toContinuousLinearMap ![0,t] :=
    (hT.differentiable (by simp) _).hasFDerivAt
  let e₀ := hT.contDiffAt.toOpenPartialHomeomorph T hd (by simp)
  let W := {x : Base | IsUnit (fderiv ℝ T x)}
  have hW : IsOpen W := Units.isOpen.preimage (hT.continuous_fderiv (by simp))
  let e := e₀.restrOpen W hW
  have he : (e : Base → Base) = T := rfl
  have htE : (![0,t] : Base) ∈ e.source :=
    ⟨hT.contDiffAt.mem_toOpenPartialHomeomorph_source hd (by simp),
      ContinuousLinearMap.isUnit_iff_bijective.mpr hD⟩
  let U := (fun s => (![0,s] : Base)) ⁻¹' e.source
  have hU : IsOpen U := e.open_source.preimage (by fun_prop)
  refine ⟨e,U,hU,htE,by simpa only [he] using hT,?_,?_⟩
  · intro y hy
    obtain ⟨u,hu⟩ := (e.map_target hy).2
    let D := ContinuousLinearEquiv.ofUnit u
    have hdy : HasFDerivAt e D.toContinuousLinearMap (e.symm y) := by
      rw [he]
      convert (hT.differentiable (by simp) _).hasFDerivAt using 1
      exact hu
    exact (e.contDiffAt_symm hy hdy (by rw [he]; exact hT.contDiffAt)).contDiffWithinAt
  · intro s hs
    refine ⟨hs,?_⟩
    change planeCurveTube c v ![0,s] = c s
    simp [planeCurveTube]

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
