import OAI.NumberTheory.CubicMoment.Theta.CubicThetaRadialEnergyNorm
import Mathlib.MeasureTheory.Integral.DominatedConvergence

namespace OAI

/-! Square-integrable domination gives convergence of the actual L2
vectors. This is used for both values and tangent coordinates. -/
noncomputable section
open Set Filter Topology MeasureTheory
namespace CubicFirstMoment

lemma cubicThetaL2_tendsto_of_dominated_sq
    {X E : Type*} [MeasurableSpace X] [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {μ : Measure X} (f : ℕ → X → E) (g : X → E)
    (hf : ∀ n, MemLp (f n) 2 μ) (hg : MemLp g 2 μ)
    (b : X → ℝ) (hb : Integrable b μ)
    (hbound : ∀ n, ∀ᵐ x ∂μ, ‖f n x-g x‖^2≤b x)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun n => f n x) atTop (𝓝 (g x))) :
    Tendsto (fun n => (hf n).toLp (f n)) atTop (𝓝 (hg.toLp g)) := by
  have hi : Tendsto (fun n => ∫ x, ‖f n x-g x‖^2 ∂μ) atTop (𝓝 0) := by
    have h := tendsto_integral_of_dominated_convergence (μ:=μ) (f:=fun _ => (0:ℝ)) b
      (fun n => ((hf n).aestronglyMeasurable.sub hg.aestronglyMeasurable).norm.pow 2) hb
      (fun n => (hbound n).mono (fun x hx => by
        change |‖f n x-g x‖^2|≤b x
        rwa [abs_of_nonneg (sq_nonneg ‖f n x-g x‖)]))
      (hlim.mono (fun x hx => by simpa using (hx.sub_const (g x)).norm.pow 2))
    simpa only [Pi.pow_apply,Pi.sub_apply,integral_zero] using h
  have he (n : ℕ) : ‖(hf n).toLp (f n)-hg.toLp g‖^2=∫ x, ‖f n x-g x‖^2 ∂μ := by
    rw [cubicTheta_l2_norm_sq_measure]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub ((hf n).toLp (f n)) (hg.toLp g),
      (hf n).coeFn_toLp,hg.coeFn_toLp] with x hx hfx hgx
    simp only [Pi.sub_apply] at hx
    rw [hx,hfx,hgx]
  have hn : Tendsto (fun n => ‖(hf n).toLp (f n)-hg.toLp g‖) atTop (𝓝 0) := by
    have h := Real.continuous_sqrt.continuousAt.tendsto.comp hi
    change Tendsto (fun n => Real.sqrt (∫ x, ‖f n x-g x‖^2 ∂μ)) atTop (𝓝 (Real.sqrt 0)) at h
    simp only [← he,Real.sqrt_sq_eq_abs,abs_norm,Real.sqrt_zero] at h
    exact h
  exact tendsto_iff_norm_sub_tendsto_zero.mpr hn

end CubicFirstMoment

end

end OAI
