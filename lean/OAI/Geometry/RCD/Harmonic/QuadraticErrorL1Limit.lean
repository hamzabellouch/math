import OAI.Geometry.RCD.Harmonic.WeightedDirectionalVanishing
import Mathlib.MeasureTheory.Integral.DominatedConvergence

namespace OAI

/-! # An integrable quadratic error bound implies local L1 convergence

This is the final scalar estimate used for mixed Hessian errors. The
gradient error enters through its integral against the fixed density.
-/

open Set Filter MeasureTheory
open scoped Topology
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ]

theorem quadratic_error_L1_limit (F G : ℕ → X → ℝ)
    (hF : ∀ k, Integrable (F k) μ) (hG : ∀ k, Integrable (G k) μ)
    {M : ℝ} (hM : 0 ≤ M)
    (hbound : ∀ k, ∀ᵐ x ∂μ, (F k x)^2 ≤ M*G k x)
    (hlim : Tendsto (fun k => ∫ x, G k x ∂μ) atTop (𝓝 0)) :
    Tendsto (fun k => ∫ x, |F k x| ∂μ) atTop (𝓝 0) := by
  have hb (k : ℕ) (r : ℝ) (_hr : 0 < r) :
      4*r*(∫ x, |F k x| ∂μ) ≤ 4*r^2*μ.real univ+M*(∫ x, G k x ∂μ) := by
    have hi := integral_mono_ae ((hF k).abs.const_mul (4*r))
      ((integrable_const (4*r^2)).add ((hG k).const_mul M))
      (hbound k |>.mono fun x hx => by
        change 4*r*|F k x| ≤ 4*r^2+M*G k x
        nlinarith [sq_nonneg (2*r-|F k x|),sq_abs (F k x)])
    simp only [Pi.add_apply] at hi
    rw [integral_const_mul,integral_add (integrable_const (4*r^2)) ((hG k).const_mul M),
      integral_const,integral_const_mul,smul_eq_mul] at hi
    nlinarith only [hi]
  have he : TendstoUniformly (fun k (_ : Unit) => ∫ x, G k x ∂μ) (fun _ => 0) atTop := by
    apply Metric.tendstoUniformly_iff.mpr
    intro ε hε
    obtain ⟨N,hN⟩ := Metric.tendsto_atTop.mp hlim ε hε
    apply eventually_atTop.mpr
    refine ⟨N,fun k hk _ => ?_⟩
    simpa only [Real.dist_eq,sub_zero,zero_sub,abs_neg] using hN k hk
  have hh := tendstoUniformly_of_directional_bound (C := μ.real univ) (M := M)
    (ENNReal.toReal_nonneg) hM
    (fun k (_ : Unit) => integral_nonneg fun x => abs_nonneg (F k x)) he
    (fun k (_ : Unit) r hr => hb k r hr)
  exact hh.tendsto_at ()

end RegularPointCoordinates

end

end OAI
