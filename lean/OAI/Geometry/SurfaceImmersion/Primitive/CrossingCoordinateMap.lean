import OAI.Geometry.SurfaceImmersion.Primitive.CrossingTargetLinear

namespace OAI

/-! The explicit map straightening two transverse surface sheets that
already use a common curve parameter as their second coordinate. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

def crossingCoordinateMap (F G : Base → ProjectionTarget 3) (z : Base × ℝ) : ProjectionTarget 3 :=
  F (crossingLeft z)+G (crossingRight z)-F (crossingAxis z)

lemma crossingCoordinateMap_smooth {F G : Base → ProjectionTarget 3}
    (hF : ContDiff ℝ ∞ F) (hG : ContDiff ℝ ∞ G) :
    ContDiff ℝ ∞ (crossingCoordinateMap F G) :=
  ((hF.comp crossingLeft.contDiff).add (hG.comp crossingRight.contDiff)).sub
    (hF.comp crossingAxis.contDiff)

lemma crossingCoordinateMap_fderiv {F G : Base → ProjectionTarget 3}
    (hF : ContDiff ℝ ∞ F) (hG : ContDiff ℝ ∞ G) (t : ℝ) :
    fderiv ℝ (crossingCoordinateMap F G) (0,t) =
      crossingTargetLinear (fderiv ℝ F ![0,t]) (fderiv ℝ G ![0,t]) := by
  have hLF : HasFDerivAt F (fderiv ℝ F ![0,t]) (crossingLeft (0,t)) := by
    rw [crossingLeft_apply]
    exact (hF.differentiable (by simp) _).hasFDerivAt
  have hRF : HasFDerivAt G (fderiv ℝ G ![0,t]) (crossingRight (0,t)) := by
    rw [crossingRight_apply]
    exact (hG.differentiable (by simp) _).hasFDerivAt
  have hAF : HasFDerivAt F (fderiv ℝ F ![0,t]) (crossingAxis (0,t)) := by
    rw [crossingAxis_apply]
    exact (hF.differentiable (by simp) _).hasFDerivAt
  have hL := hLF.comp (0,t) crossingLeft.hasFDerivAt
  have hR := hRF.comp (0,t) crossingRight.hasFDerivAt
  have hA := hAF.comp (0,t) crossingAxis.hasFDerivAt
  exact ((hL.add hR).sub hA).fderiv

lemma common_axis_derivatives {F G : Base → ProjectionTarget 3}
    (hF : ContDiff ℝ ∞ F) (hG : ContDiff ℝ ∞ G) (t : ℝ)
    (he : (fun s => F ![0,s]) =ᶠ[𝓝 t] (fun s => G ![0,s])) :
    fderiv ℝ F ![0,t] ![0,1] = fderiv ℝ G ![0,t] ![0,1] := by
  let L : ℝ →L[ℝ] Base := ContinuousLinearMap.pi ![0,ContinuousLinearMap.id ℝ ℝ]
  have hL : ∀ s, L s = ![0,s] := by
    intro s
    ext i
    fin_cases i <;> rfl
  have hEq : F ∘ L =ᶠ[𝓝 t] G ∘ L := by
    filter_upwards [he] with s hs
    simpa only [Function.comp_apply,hL] using hs
  have hD : fderiv ℝ (F ∘ L) t = fderiv ℝ (G ∘ L) t := hEq.fderiv_eq
  rw [fderiv_comp t (hF.differentiable (by simp) _) L.differentiableAt,
    fderiv_comp t (hG.differentiable (by simp) _) L.differentiableAt,L.fderiv] at hD
  simpa only [ContinuousLinearMap.comp_apply,hL] using
    congrArg (fun D : ℝ →L[ℝ] ProjectionTarget 3 => D 1) hD

theorem crossingCoordinateMap_regular {F G : Base → ProjectionTarget 3}
    (hF : ContDiff ℝ ∞ F) (hG : ContDiff ℝ ∞ G) (t : ℝ)
    (he : (fun s => F ![0,s]) =ᶠ[𝓝 t] (fun s => G ![0,s]))
    (hs : Function.Surjective (fun z : Base × Base =>
      fderiv ℝ F ![0,t] z.1-fderiv ℝ G ![0,t] z.2)) :
    Function.Bijective (fderiv ℝ (crossingCoordinateMap F G) (0,t)) := by
  rw [crossingCoordinateMap_fderiv hF hG]
  exact crossingTargetLinear_bijective _ _ (common_axis_derivatives hF hG t he) hs

lemma crossingCoordinateMap_left {F G : Base → ProjectionTarget 3} {t : ℝ}
    (he : F ![0,t] = G ![0,t]) (u : ℝ) :
    crossingCoordinateMap F G (![u,0],t) = F ![u,t] := by
  rw [crossingCoordinateMap,crossingLeft_apply,crossingRight_apply,crossingAxis_apply]
  simp only [Matrix.cons_val_zero,Matrix.cons_val_one]
  rw [he,add_sub_cancel_right]

lemma crossingCoordinateMap_right (F G : Base → ProjectionTarget 3) (v t : ℝ) :
    crossingCoordinateMap F G (![0,v],t) = G ![v,t] := by
  rw [crossingCoordinateMap,crossingLeft_apply,crossingRight_apply,crossingAxis_apply]
  simp only [Matrix.cons_val_zero,Matrix.cons_val_one]
  abel

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
