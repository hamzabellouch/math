import OAI.Geometry.SurfaceImmersion.Whitney.FramedCurveTube
import Mathlib.Analysis.Calculus.ContDiff.Deriv

namespace OAI

/-! A smooth transverse field gives an actual target tube whose central
 coordinate plane is exactly the ruled surface. -/
noncomputable section
open Set Filter Matrix
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

def varyingFramedCurveTube (c a : ℝ → (Fin 3 → ℝ)) (z : Base × ℝ) : Fin 3 → ℝ :=
  c z.2 + z.1 0 • a z.2 + z.1 1 • (deriv c z.2 ⨯₃ a z.2)

lemma varyingFrameCross_smooth {c a : ℝ → (Fin 3 → ℝ)}
    (hc : ContDiff ℝ ∞ c) (ha : ContDiff ℝ ∞ a) :
    ContDiff ℝ ∞ (fun t => deriv c t ⨯₃ a t) := by
  have hdc : ContDiff ℝ ∞ (deriv c) := hc.deriv'
  apply contDiff_pi.mpr
  intro i
  fin_cases i <;> dsimp [cross_apply] <;> fun_prop

lemma varyingFramedCurveTube_smooth {c a : ℝ → (Fin 3 → ℝ)}
    (hc : ContDiff ℝ ∞ c) (ha : ContDiff ℝ ∞ a) :
    ContDiff ℝ ∞ (varyingFramedCurveTube c a) := by
  have hw := varyingFrameCross_smooth hc ha
  exact ((hc.comp contDiff_snd).add
    (((contDiff_apply ℝ ℝ 0).comp contDiff_fst).smul (ha.comp contDiff_snd))).add
      (((contDiff_apply ℝ ℝ 1).comp contDiff_fst).smul (hw.comp contDiff_snd))

lemma varyingFramedCurveTube_fderiv {c a : ℝ → (Fin 3 → ℝ)}
    (hc : ContDiff ℝ ∞ c) (ha : ContDiff ℝ ∞ a) (t : ℝ) :
    fderiv ℝ (varyingFramedCurveTube c a) (0,t) = curveNormalLinear (deriv c t) (a t) := by
  let z : Base × ℝ := (0,t)
  have hC := ((hc.differentiable (by simp) t).hasFDerivAt).comp z
    (hasFDerivAt_snd (𝕜 := ℝ) (p := z))
  have hA := ((ha.differentiable (by simp) t).hasFDerivAt).comp z
    (hasFDerivAt_snd (𝕜 := ℝ) (p := z))
  have h0 := (hasFDerivAt_apply (𝕜 := ℝ) (0 : Fin 2) (0 : Base)).comp z
    (hasFDerivAt_fst (𝕜 := ℝ) (p := z))
  have h1 := (hasFDerivAt_apply (𝕜 := ℝ) (1 : Fin 2) (0 : Base)).comp z
    (hasFDerivAt_fst (𝕜 := ℝ) (p := z))
  have hW := (((varyingFrameCross_smooth hc ha).differentiable (by simp) t).hasFDerivAt).comp z
    (hasFDerivAt_snd (𝕜 := ℝ) (p := z))
  have hd := (hC.add (h0.smul hA)).add (h1.smul hW)
  change HasFDerivAt (varyingFramedCurveTube c a) _ (0,t) at hd
  rw [hd.fderiv]
  apply ContinuousLinearMap.ext
  intro w
  simp [curveNormalLinear_apply,z,fderiv_eq_smul_deriv]

lemma varyingFramedCurveTube_regular_axis {c a : ℝ → (Fin 3 → ℝ)}
    (hc : ContDiff ℝ ∞ c) (ha : ContDiff ℝ ∞ a) {t : ℝ}
    (hv : deriv c t ≠ 0) (htrans : ∀ r : ℝ, r • deriv c t ≠ a t) :
    Function.Bijective (fderiv ℝ (varyingFramedCurveTube c a) (0,t)) := by
  rw [varyingFramedCurveTube_fderiv hc ha]
  exact curveNormalLinear_bijective hv htrans

lemma varyingFramedCurveTube_zero_normal (c a : ℝ → (Fin 3 → ℝ)) (x t : ℝ) :
    varyingFramedCurveTube c a (![x,0],t) = c t + x • a t := by
  simp [varyingFramedCurveTube]

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
