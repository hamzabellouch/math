import OAI.Analysis.CircleDomains.Sobolev.SmoothLogarithmicModulus

namespace OAI

/-! Passing the smooth annular estimate through uniform approximation
and convergence of the actual Dirichlet energies. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

 theorem homeomorphic_height_log_bound_of_smooth_approximation (φ : ℂ ≃ₜ ℂ) (c : ℂ)
    (f : ℕ → ℂ → ℝ) (hf : ∀ n, ContDiff ℝ 1 (f n))
    {r R E : ℝ} (hr : 0 < r) (hrR : r ≤ R)
    (huniform : ∀ ε > 0, ∀ᶠ n in atTop,
      ∀ z ∈ closedBall c R, |(φ z).im-f n z| ≤ ε)
    (henergy : Tendsto (fun n => ∫ z in {z : ℂ | r < dist z c ∧ dist z c < R},
      ‖fderiv ℝ (f n) z‖^2) atTop (𝓝 E))
    {x y : ℂ} (hx : x ∈ closedBall c r) (hy : y ∈ closedBall c r) :
    |(φ x).im-(φ y).im|^2 * Real.log (R/r) ≤ 16*Real.pi*E := by
  have he (ε : ℝ) (hε : 0 < ε) :
      (|(φ x).im-(φ y).im|^2-8*ε^2)*Real.log (R/r) ≤ 16*Real.pi*E := by
    apply ge_of_tendsto ((tendsto_const_nhds (x := 16*Real.pi)).mul henergy)
    filter_upwards [huniform ε hε] with n hn
    exact homeomorphic_pair_logarithmic_smooth_bound φ c (hf n) hr hrR hε.le hn hx hy
  have hzero : Tendsto (fun n : ℕ => (1 : ℝ)/((n : ℝ)+1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have ht := (((tendsto_const_nhds (x := |(φ x).im-(φ y).im|^2)).sub
    ((tendsto_const_nhds (x := (8 : ℝ))).mul (hzero.pow 2))).mul
    (tendsto_const_nhds (x := Real.log (R/r))))
  have hle := le_of_tendsto ht (Eventually.of_forall (fun n => he (1/((n : ℝ)+1))
    (by positivity)))
  simpa only [zero_pow (by decide : 2 ≠ 0), mul_zero, sub_zero] using hle

end CircleDomainRigidity

end

end OAI
