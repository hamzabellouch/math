import OAI.NumberTheory.Ostmann.Dirichlet.SmoothedExplicitInversion
import OAI.NumberTheory.Ostmann.Dirichlet.Zeros

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

namespace Ostmann.Dirichlet
open MeasureTheory Filter
open scoped Topology SchwartzMap

variable (ρ : 𝓢(ℝ, ℂ))
local notation "smoothKernel" => mellin (ρ : ℝ → ℂ)

noncomputable def characterSmoothIntegrand {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) (X : ℝ) (s : ℂ) : ℂ :=
  -logDeriv (DirichletCharacter.LFunction chi) s * smoothKernel s * (X:ℂ)^s

lemma norm_characterSmoothIntegrand {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    {X : ℝ} (hX : 0 < X) (s : ℂ) :
    ‖characterSmoothIntegrand ρ chi X s‖ =
      ‖logDeriv (DirichletCharacter.LFunction chi) s‖ * ‖smoothKernel s‖ * X^s.re := by
  unfold characterSmoothIntegrand
  rw [norm_mul,norm_mul,norm_neg,Complex.norm_cpow_eq_rpow_re_of_pos hX]

lemma differentiableAt_characterSmoothIntegrand {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) (hchi : chi ≠ 1) {X : ℝ} (hX : 0 < X)
    {s : ℂ} (hs : 0 < s.re) (hne : DirichletCharacter.LFunction chi s ≠ 0) :
    DifferentiableAt ℂ (characterSmoothIntegrand ρ chi X) s := by
  have hL := DirichletCharacter.differentiable_LFunction hchi
  have hder : DifferentiableAt ℂ (deriv (DirichletCharacter.LFunction chi)) s :=
    (hL.analyticAt s).deriv.differentiableAt
  have hlog : DifferentiableAt ℂ (fun z => -logDeriv (DirichletCharacter.LFunction chi) z) s := by
    change DifferentiableAt ℂ (fun z => -(deriv (DirichletCharacter.LFunction chi) z /
      DirichletCharacter.LFunction chi z)) s
    exact (hder.div hL.differentiableAt hne).neg
  have hXC : (X:ℂ) ≠ 0 := by exact_mod_cast hX.ne'
  have hpow : DifferentiableAt ℂ (fun z:ℂ => (X:ℂ)^z) s := by
    simp_rw [Complex.cpow_def_of_ne_zero hXC]
    fun_prop
  exact (hlog.mul (schwartz_mellin_differentiableAt ρ hs)).mul hpow

lemma continuous_characterSmooth_right {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) (hchi : chi ≠ 1) {sigma X : ℝ}
    (hs : 1 < sigma) (hX : 0 < X) :
    Continuous (fun t:ℝ => characterSmoothIntegrand ρ chi X ((sigma:ℂ)+(t:ℂ)*Complex.I)) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  have hre : ((sigma:ℂ)+(t:ℂ)*Complex.I).re = sigma := by simp
  exact (differentiableAt_characterSmoothIntegrand ρ chi hchi hX (by rw [hre]; linarith)
    (LFunction_ne_zero_right chi (by simpa only [hre] using hs))).continuousAt.comp (by fun_prop)

lemma integrable_characterSmooth_right {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) (hchi : chi ≠ 1) {sigma X : ℝ}
    (hs : 1 < sigma) (hX : 0 < X) :
    Integrable (fun t:ℝ => characterSmoothIntegrand ρ chi X ((sigma:ℂ)+(t:ℂ)*Complex.I)) := by
  obtain ⟨C,hC,hbound⟩ := uniform_log_derivative_right
  have hg := (schwartz_mellin_vertical_integrable ρ sigma (by linarith : 0 < sigma)).norm.const_mul
    (((sigma-1)⁻¹+C)*X^sigma)
  apply hg.mono' (continuous_characterSmooth_right ρ chi hchi hs hX).aestronglyMeasurable
  filter_upwards [] with t
  have hre : ((sigma:ℂ)+(t:ℂ)*Complex.I).re = sigma := by simp
  have hb := hbound q chi ((sigma:ℂ)+(t:ℂ)*Complex.I) (by simpa only [hre] using hs)
  rw [norm_characterSmoothIntegrand ρ chi hX,hre]
  change ‖logDeriv (DirichletCharacter.LFunction chi) ((sigma:ℂ)+(t:ℂ)*Complex.I)‖ * _ * _ ≤ _
  have hb' : ‖logDeriv (DirichletCharacter.LFunction chi) ((sigma:ℂ)+(t:ℂ)*Complex.I)‖ ≤
      (sigma-1)⁻¹+C := by simpa only [logDeriv_apply,hre] using hb
  calc
    _ ≤ ((sigma-1)⁻¹+C)*‖smoothKernel ((sigma:ℂ)+(t:ℂ)*Complex.I)‖*X^sigma := by gcongr
    _ = _ := by ring

end Ostmann.Dirichlet

end OAI
