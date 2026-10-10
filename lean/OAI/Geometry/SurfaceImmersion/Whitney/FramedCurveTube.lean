import OAI.Geometry.SurfaceImmersion.Geometry.CurveNormalFrame

namespace OAI

/-! Explicit smooth target tubes around regular curves. -/
noncomputable section
open Set Filter Matrix
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

def framedCurveTube (c : ℝ → (Fin 3 → ℝ)) (a : Fin 3 → ℝ)
    (z : Base × ℝ) : Fin 3 → ℝ :=
  c z.2 + z.1 0 • a + z.1 1 • (deriv c z.2 ⨯₃ a)

lemma curve_cross_velocity_smooth {c : ℝ → (Fin 3 → ℝ)} (hc : ContDiff ℝ ∞ c)
    (a : Fin 3 → ℝ) : ContDiff ℝ ∞ (fun t => deriv c t ⨯₃ a) := by
  have hv : ContDiff ℝ ∞ (deriv c) := (contDiff_infty_iff_deriv.mp hc).2
  apply contDiff_pi.mpr
  intro i
  fin_cases i <;> dsimp [cross_apply] <;> fun_prop

lemma framedCurveTube_smooth {c : ℝ → (Fin 3 → ℝ)} (hc : ContDiff ℝ ∞ c)
    (a : Fin 3 → ℝ) : ContDiff ℝ ∞ (framedCurveTube c a) := by
  have hw := curve_cross_velocity_smooth hc a
  exact ((hc.comp contDiff_snd).add
    (((contDiff_apply ℝ ℝ 0).comp contDiff_fst).smul contDiff_const)).add
      (((contDiff_apply ℝ ℝ 1).comp contDiff_fst).smul (hw.comp contDiff_snd))

lemma framedCurveTube_fderiv {c : ℝ → (Fin 3 → ℝ)} (hc : ContDiff ℝ ∞ c)
    (a : Fin 3 → ℝ) (t : ℝ) :
    fderiv ℝ (framedCurveTube c a) (0,t) = curveNormalLinear (deriv c t) a := by
  let z : Base × ℝ := (0,t)
  have hC := ((hc.differentiable (by simp) t).hasFDerivAt).comp z
    (hasFDerivAt_snd (𝕜 := ℝ) (p := z))
  have h0 := (hasFDerivAt_apply (𝕜 := ℝ) (0 : Fin 2) (0 : Base)).comp z
    (hasFDerivAt_fst (𝕜 := ℝ) (p := z))
  have h1 := (hasFDerivAt_apply (𝕜 := ℝ) (1 : Fin 2) (0 : Base)).comp z
    (hasFDerivAt_fst (𝕜 := ℝ) (p := z))
  have hW := (((curve_cross_velocity_smooth hc a).differentiable (by simp) t).hasFDerivAt).comp z
    (hasFDerivAt_snd (𝕜 := ℝ) (p := z))
  have hd := (hC.add (h0.smul_const a)).add (h1.smul hW)
  change HasFDerivAt (framedCurveTube c a) _ (0,t) at hd
  rw [hd.fderiv]
  apply ContinuousLinearMap.ext
  intro w
  simp [curveNormalLinear_apply,z,fderiv_eq_smul_deriv]

lemma framedCurveTube_regular_axis {c : ℝ → (Fin 3 → ℝ)} (hc : ContDiff ℝ ∞ c)
    {a : Fin 3 → ℝ} (ha : ∀ t r : ℝ, r • deriv c t ≠ a) (t : ℝ)
    (ht : deriv c t ≠ 0) :
    Function.Bijective (fderiv ℝ (framedCurveTube c a) (0,t)) := by
  rw [framedCurveTube_fderiv hc]
  exact curveNormalLinear_bijective ht (ha t)

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
