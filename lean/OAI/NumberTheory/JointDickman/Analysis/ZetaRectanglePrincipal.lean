import OAI.NumberTheory.JointDickman.Analysis.AnalyticLogUniqueness
import OAI.NumberTheory.JointDickman.Analysis.ZetaRectangleLog
import OAI.NumberTheory.JointDickman.Analysis.SquarefreeRieszSingularFactor
import OAI.NumberTheory.JointDickman.Analysis.SquarefreeRieszKernel

namespace OAI

/-! # Uniform local identification of normalized rectangle logarithms -/
namespace JointDickman
open Complex Set

theorem zeta_rectangle_principal_local : ∃ r : ℝ, 0 < r ∧
    ∀ {δ T : ℝ}, 0 < δ → 0 < T → ∀ {f : ℂ → ℂ},
      AnalyticOnNhd ℂ f (zetaOpenRectangle δ T) → f 1 = 0 →
      (∀ s ∈ zetaOpenRectangle δ T, exp (f s) = zetaPoleFactor s) →
      ∀ s ∈ Metric.ball (1:ℂ) r ∩ zetaOpenRectangle δ T,
        f s = log (zetaPoleFactor s) := by
  have hopen : IsOpen (zetaPoleFactor ⁻¹' slitPlane) :=
    isOpen_slitPlane.preimage zetaPoleFactor_differentiable.continuous
  obtain ⟨r,hr,hsub⟩ := Metric.mem_nhds_iff.mp (hopen.mem_nhds
    (show (1:ℂ) ∈ zetaPoleFactor ⁻¹' slitPlane by
      simpa only [mem_preimage,zetaPoleFactor_one] using one_mem_slitPlane))
  refine ⟨r,hr,?_⟩
  intro δ T hδ hT f hf hf1 he s hs
  let U := Metric.ball (1:ℂ) r ∩ zetaOpenRectangle δ T
  have hU : IsOpen U := Metric.isOpen_ball.inter (zetaOpenRectangle_isOpen δ T)
  have hconv : Convex ℝ U := (convex_ball (1:ℂ) r).inter (zetaOpenRectangle_convex δ T)
  have h1 : (1:ℂ) ∈ U := ⟨Metric.mem_ball_self hr,zetaOpenRectangle_one hδ hT⟩
  have hg : AnalyticOnNhd ℂ (fun s => log (zetaPoleFactor s)) U := by
    intro s hs
    exact (zetaPoleFactor_differentiable.analyticAt s).clog (hsub hs.1)
  have hh := analytic_log_unique hU hconv.isPreconnected
    (hf.mono inter_subset_right) hg
    (fun s hs => (he s hs.2).trans (Complex.exp_log (slitPlane_ne_zero (hsub hs.1))).symm)
    h1 (by simp only [hf1,zetaPoleFactor_one,log_one])
  exact hh hs

theorem squarefreeRieszKernel_local_uniform : ∃ r : ℝ, 0 < r ∧
    ∀ {δ T : ℝ}, 0 < δ → 0 < T → ∀ {f : ℂ → ℂ},
      AnalyticOnNhd ℂ f (zetaOpenRectangle δ T) → f 1 = 0 →
      (∀ s ∈ zetaOpenRectangle δ T, exp (f s) = zetaPoleFactor s) →
      ∀ (z L : ℝ) (w : ℂ), 1+w ∈ Metric.ball (1:ℂ) r ∩ zetaOpenRectangle δ T →
        squarefreeRieszKernel z L f w =
          exp ((L:ℂ)*w)*squarefreeRieszSingularFactor z (1+w) := by
  obtain ⟨r,hr,hprincipal⟩ := zeta_rectangle_principal_local
  refine ⟨r,hr,?_⟩
  intro δ T hδ hT f hf hf1 he z L w hw
  have h := hprincipal hδ hT hf hf1 he (1+w) hw
  simp only [squarefreeRieszKernel,squarefreeRieszSingularFactor,squarefreeSingularFactor,h]
  have heq : (1:ℂ)+w+1 = 2+w := by ring
  rw [heq]
  simp only [div_eq_mul_inv,mul_inv_rev]
  ring

end JointDickman

end OAI
