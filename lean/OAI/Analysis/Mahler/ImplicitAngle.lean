import OAI.Analysis.Mahler.VerticalSpeed
import OAI.Analysis.Mahler.AngularGeometry
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.Complex.CauchyIntegral

namespace OAI

namespace SymmetricMahler
open Real Complex Set Filter
open scoped Topology ContDiff

/-- The scalar implicit function theorem with the angular nonzero derivative
as its explicit hypothesis. -/
theorem exists_local_real_level {f : ℝ × ℝ → ℝ} {a b c : ℝ}
    (hC : ContDiffAt ℝ ∞ f (a,b))
    (hD : HasDerivAt (fun y => f (a,y)) c b) (hc : c ≠ 0) :
    ∃ θ : ℝ → ℝ, θ a = b ∧ ContDiffAt ℝ ∞ θ a ∧
      ∀ᶠ r in 𝓝 a, f (r,θ r) = f (a,b) := by
  let D := fderiv ℝ f (a,b) ∘L ContinuousLinearMap.inr ℝ ℝ ℝ
  have hfd : HasFDerivAt (fun y => f (a,y)) D b :=
    (hC.differentiableAt (by norm_num)).hasFDerivAt.comp b (hasFDerivAt_prodMk_right a b)
  have heq := hfd.unique hD.hasFDerivAt
  have hval (x : ℝ) : D x = x*c := by
    rw [heq]
    simp
  have hinj : Function.Injective D := by
    intro x y h
    rw [hval, hval] at h
    exact mul_right_cancel₀ hc h
  have hsurj : Function.Surjective D := by
    intro x
    refine ⟨x/c, ?_⟩
    rw [hval]
    field_simp
  have hInv : D.IsInvertible := by
    refine ⟨ContinuousLinearEquiv.ofBijective D (LinearMap.ker_eq_bot.mpr hinj)
      (LinearMap.range_eq_top.mpr hsurj), ?_⟩
    rfl
  refine ⟨hC.implicitFunction (by norm_num) hInv, ?_, ?_, ?_⟩
  · exact hC.implicitFunction_apply_self (by norm_num) hInv
  · exact hC.contDiffAt_implicitFunction (by norm_num) hInv
  · exact hC.eventually_apply_implicitFunction (by norm_num) hInv

lemma contDiffAt_Q_uncurry {r θ : ℝ} (hr : 0 < r) (hr1 : r < 1) :
    ContDiffAt ℝ ∞ (fun p : ℝ × ℝ => MahlerConformal.Q p.1 p.2) (r,θ) := by
  have hw : ‖MahlerConformal.polar r θ‖ < 1 := by
    rwa [MahlerConformal.norm_polar hr.le]
  have hF : ContDiffAt ℂ ∞ MahlerConformal.F (MahlerConformal.polar r θ) :=
    (MahlerConformal.differentiableOn_F.analyticAt (Metric.isOpen_ball.mem_nhds (by simpa using hw))).contDiffAt
  have hFR := hF.restrict_scalars ℝ
  have hp : ContDiffAt ℝ ∞ (fun p : ℝ × ℝ => MahlerConformal.polar p.1 p.2) (r,θ) := by
    have hfst : ContDiffAt ℝ ∞ (fun p : ℝ × ℝ => (p.1 : ℂ)) (r,θ) :=
      Complex.ofRealCLM.contDiff.contDiffAt.comp (r,θ) contDiffAt_fst
    have hsnd : ContDiffAt ℝ ∞ (fun p : ℝ × ℝ => (p.2 : ℂ)) (r,θ) :=
      Complex.ofRealCLM.contDiff.contDiffAt.comp (r,θ) contDiffAt_snd
    exact hfst.mul ((hsnd.mul contDiffAt_const).cexp)
  have hcomp := hFR.comp (r,θ) hp
  exact Complex.reCLM.contDiff.contDiffAt.comp (r,θ) hcomp

lemma contDiffAt_S_uncurry {r θ : ℝ} (hr : 0 < r) (hr1 : r < 1) :
    ContDiffAt ℝ ∞ (fun p : ℝ × ℝ => MahlerConformal.S p.1 p.2) (r,θ) := by
  have hw : ‖MahlerConformal.polar r θ‖ < 1 := by
    rwa [MahlerConformal.norm_polar hr.le]
  have hF : ContDiffAt ℂ ∞ MahlerConformal.F (MahlerConformal.polar r θ) :=
    (MahlerConformal.differentiableOn_F.analyticAt (Metric.isOpen_ball.mem_nhds (by simpa using hw))).contDiffAt
  have hFR := hF.restrict_scalars ℝ
  have hp : ContDiffAt ℝ ∞ (fun p : ℝ × ℝ => MahlerConformal.polar p.1 p.2) (r,θ) := by
    have hfst : ContDiffAt ℝ ∞ (fun p : ℝ × ℝ => (p.1 : ℂ)) (r,θ) :=
      Complex.ofRealCLM.contDiff.contDiffAt.comp (r,θ) contDiffAt_fst
    have hsnd : ContDiffAt ℝ ∞ (fun p : ℝ × ℝ => (p.2 : ℂ)) (r,θ) :=
      Complex.ofRealCLM.contDiff.contDiffAt.comp (r,θ) contDiffAt_snd
    exact hfst.mul ((hsnd.mul contDiffAt_const).cexp)
  have hcomp := hFR.comp (r,θ) hp
  exact Complex.imCLM.contDiff.contDiffAt.comp (r,θ) hcomp

/-- A smooth local angular fiber exists at every point of the upper half-disk.
This instantiates the implicit theorem with the actual power-series real part. -/
theorem exists_local_angle {r θ : ℝ} (hr : 0 < r) (hr1 : r < 1)
    (hθ : 0 < θ) (hθπ : θ < Real.pi) :
    ∃ ψ : ℝ → ℝ, ψ r = θ ∧ ContDiffAt ℝ ∞ ψ r ∧
      ∀ᶠ s in 𝓝 r, MahlerConformal.Q s (ψ s) = MahlerConformal.Q r θ := by
  apply exists_local_real_level (contDiffAt_Q_uncurry hr hr1)
    (MahlerConformal.hasDerivAt_Q hr hr1 θ)
  exact neg_ne_zero.mpr (MahlerConformal.B_pos hr hr1 hθ hθπ).ne'

end SymmetricMahler

end OAI
