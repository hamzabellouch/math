import OAI.Analysis.LipschitzHilbert.Fourier.SincMaskMotion
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic

namespace OAI

/-! Smooth sinc multipliers preserve Schwartz packets. The derivative
bounds follow from the same compact cosine average used for the mask's
Fourier support; no assertion about a singular quotient at zero is used. -/

noncomputable section
open MeasureTheory Set
open scoped ContDiff Topology
namespace LipschitzHilbert

private def sincJet (n : ℕ) (x : ℝ) : ℝ :=
  ∫ t in Ioc (0:ℝ) 1, t^n*Real.cos (t*x+(n:ℝ)*Real.pi/2)

private theorem sincJet_integrand_bound (n : ℕ) (x t : ℝ) (ht : t ∈ Ioc (0:ℝ) 1) :
    ‖t^n*Real.cos (t*x+(n:ℝ)*Real.pi/2)‖ ≤ 1 := by
  rw [Real.norm_eq_abs,abs_mul,abs_pow,abs_of_pos ht.1]
  exact (mul_le_mul (pow_le_one₀ ht.1.le ht.2) (Real.abs_cos_le_one _)
    (abs_nonneg _) zero_le_one).trans_eq (one_mul 1)

private theorem sincJet_integrable (n : ℕ) (x : ℝ) :
    Integrable (fun t => t^n*Real.cos (t*x+(n:ℝ)*Real.pi/2))
      (volume.restrict (Ioc (0:ℝ) 1)) := by
  apply (integrable_const (1:ℝ)).mono'
  · exact (by fun_prop : Continuous (fun t : ℝ =>
      t^n*Real.cos (t*x+(n:ℝ)*Real.pi/2))).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact sincJet_integrand_bound n x t ht

private theorem sincJet_bound (n : ℕ) (x : ℝ) : ‖sincJet n x‖ ≤ 1 := by
  have h := norm_integral_le_of_norm_le (integrable_const (1:ℝ))
    (show ∀ᵐ t ∂volume.restrict (Ioc (0:ℝ) 1),
      ‖t^n*Real.cos (t*x+(n:ℝ)*Real.pi/2)‖ ≤ 1 by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      exact sincJet_integrand_bound n x t ht)
  simpa [sincJet] using h

private theorem sincJet_continuous (n : ℕ) : Continuous (sincJet n) := by
  apply continuous_of_dominated (bound := fun _ : ℝ => (1:ℝ))
  · intro x
    exact (sincJet_integrable n x).aestronglyMeasurable
  · intro x
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact sincJet_integrand_bound n x t ht
  · exact integrable_const _
  · exact Filter.Eventually.of_forall (fun t => by fun_prop)

private theorem sincJet_hasDerivAt (n : ℕ) (x : ℝ) :
    HasDerivAt (sincJet n) (sincJet (n+1) x) x := by
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Ioc (0:ℝ) 1)) (s := univ)
    (F := fun x t : ℝ => t^n*Real.cos (t*x+(n:ℝ)*Real.pi/2))
    (F' := fun x t : ℝ => t^(n+1)*Real.cos (t*x+((n+1:ℕ):ℝ)*Real.pi/2))
    (bound := fun _ => (1:ℝ))
    (show univ ∈ nhds x from Filter.univ_mem)
    (Filter.Eventually.of_forall (fun y => (sincJet_integrable n y).aestronglyMeasurable))
    (sincJet_integrable n x) (sincJet_integrable (n+1) x).aestronglyMeasurable
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      intro y _
      exact sincJet_integrand_bound (n+1) y t ht)
    (integrable_const _) (by
      filter_upwards [] with t
      intro y _
      have hd := (((hasDerivAt_id y).const_mul t).add_const
        ((n:ℝ)*Real.pi/2)).cos.const_mul (t^n)
      simp only [id_eq,mul_one] at hd
      convert hd using 1
      have hc : Real.cos (t*y+((n+1:ℕ):ℝ)*Real.pi/2) =
          -Real.sin (t*y+(n:ℝ)*Real.pi/2) := by
        rw [show t*y+((n+1:ℕ):ℝ)*Real.pi/2 =
          (t*y+(n:ℝ)*Real.pi/2)+Real.pi/2 by push_cast; ring,
          Real.cos_add_pi_div_two]
      rw [hc,pow_succ]
      ring)
  exact h.2

private theorem sincJet_deriv (n : ℕ) : deriv (sincJet n) = sincJet (n+1) := by
  funext x
  exact (sincJet_hasDerivAt n x).deriv

private theorem sincJet_contDiff (n : ℕ) : ContDiff ℝ ∞ (sincJet n) := by
  rw [contDiff_infty]
  intro k
  induction k generalizing n with
  | zero => exact contDiff_zero.mpr (sincJet_continuous n)
  | succ k ih =>
      rw [Nat.cast_add,Nat.cast_one,contDiff_succ_iff_deriv]
      refine ⟨fun x => (sincJet_hasDerivAt n x).differentiableAt,?_,?_⟩
      · simp
      · rw [sincJet_deriv]
        exact ih (n+1)

private theorem sincJet_zero : sincJet 0 = Real.sinc := by
  funext x
  rw [sinc_eq_integral_cos,intervalIntegral.integral_of_le zero_le_one]
  simp only [sincJet,pow_zero,Nat.cast_zero,zero_mul,zero_div,add_zero,one_mul]

private theorem sincJet_iteratedDeriv (n : ℕ) : iteratedDeriv n Real.sinc = sincJet n := by
  induction n with
  | zero => simp only [iteratedDeriv_zero,sincJet_zero]
  | succ n ih => rw [iteratedDeriv_succ,ih,sincJet_deriv]

/-- All real sinc derivatives are uniformly bounded by one. -/
theorem norm_iteratedDeriv_sinc_le_one (n : ℕ) (x : ℝ) :
    ‖iteratedDeriv n Real.sinc x‖ ≤ 1 := by
  rw [sincJet_iteratedDeriv]
  exact sincJet_bound n x

theorem sinc_hasTemperateGrowth : Function.HasTemperateGrowth Real.sinc := by
  refine ⟨?_,fun n => ⟨0,1,fun x => ?_⟩⟩
  · rw [← sincJet_zero]
    exact sincJet_contDiff 0
  · simpa only [norm_iteratedFDeriv_eq_norm_iteratedDeriv,pow_zero,mul_one] using
      norm_iteratedDeriv_sinc_le_one n x

theorem affineSinc_hasTemperateGrowth (a b : ℝ) :
    Function.HasTemperateGrowth (fun x : ℝ => (Real.sinc (a*x+b):ℂ)) := by
  apply Complex.hasTemperateGrowth_ofReal.comp
  exact sinc_hasTemperateGrowth.comp (by fun_prop)

/-- The genuine affine sinc multiplier applied to a Schwartz packet. -/
def affineSincSchwartz (f : SchwartzMap ℝ ℂ) (a b : ℝ) : SchwartzMap ℝ ℂ :=
  SchwartzMap.smulLeftCLM ℂ (fun x : ℝ => (Real.sinc (a*x+b):ℂ)) f

@[simp] theorem affineSincSchwartz_apply (f : SchwartzMap ℝ ℂ) (a b x : ℝ) :
    affineSincSchwartz f a b x = (Real.sinc (a*x+b):ℂ)*f x := by
  exact SchwartzMap.smulLeftCLM_apply_apply (affineSinc_hasTemperateGrowth a b) f x

theorem sincProductAffine_hasTemperateGrowth (n : ℕ) (a b c d : ℝ) :
    Function.HasTemperateGrowth
      (fun x : ℝ => (sincProductMask n (a*x+b) (c*x+d):ℂ)) := by
  apply Complex.hasTemperateGrowth_ofReal.comp
  exact ((sinc_hasTemperateGrowth.comp (by fun_prop)).mul
    (sinc_hasTemperateGrowth.comp (by fun_prop))).pow (2*n)

/-- Multiplication by the actual even mask is a Schwartz operation. -/
def sincProductSchwartz (f : SchwartzMap ℝ ℂ) (n : ℕ) (a b c d : ℝ) : SchwartzMap ℝ ℂ :=
  SchwartzMap.smulLeftCLM ℂ
    (fun x : ℝ => (sincProductMask n (a*x+b) (c*x+d):ℂ)) f

@[simp] theorem sincProductSchwartz_apply (f : SchwartzMap ℝ ℂ)
    (n : ℕ) (a b c d x : ℝ) :
    sincProductSchwartz f n a b c d x = (sincProductMask n (a*x+b) (c*x+d):ℂ)*f x := by
  exact SchwartzMap.smulLeftCLM_apply_apply
    (sincProductAffine_hasTemperateGrowth n a b c d) f x

theorem sincProductSchwartz_norm_le (f : SchwartzMap ℝ ℂ)
    (n : ℕ) (a b c d x : ℝ) :
    ‖sincProductSchwartz f n a b c d x‖ ≤ ‖f x‖ := by
  rw [sincProductSchwartz_apply,norm_mul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (sincProductMask_nonneg _ _ _)]
  exact mul_le_of_le_one_left (norm_nonneg _) (sincProductMask_le_one _ _ _)

theorem sincProductAffine_lipschitz (n : ℕ) (a b c d : ℝ) :
    LipschitzWith ⟨2*(n:ℝ)*(|a|+|c|),by positivity⟩
      (fun x : ℝ => (sincProductMask n (a*x+b) (c*x+d):ℂ)) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have h := sincProductMask_motion n (a*x+b) (c*x+d) (a*y+b) (c*y+d)
  have ha : |a*x+b-(a*y+b)| = |a| * |x-y| := by
    rw [show a*x+b-(a*y+b) = a*(x-y) by ring,abs_mul]
  have hc : |c*x+d-(c*y+d)| = |c| * |x-y| := by
    rw [show c*x+d-(c*y+d) = c*(x-y) by ring,abs_mul]
  rw [ha,hc] at h
  simp only [dist_eq_norm,← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs]
  change |sincProductMask n (a*x+b) (c*x+d)-sincProductMask n (a*y+b) (c*y+d)| ≤
    (2*(n:ℝ)*(|a|+|c|))*|x-y|
  calc
    _ ≤ 2*(n:ℝ)*(|a| * |x-y|+|c| * |x-y|) := h
    _ = _ := by ring

/-- The extra derivative cost is precisely the sum of mask slopes. -/
theorem sincProductSchwartz_deriv_le (f : SchwartzMap ℝ ℂ)
    (n : ℕ) (a b c d x : ℝ) :
    ‖deriv (sincProductSchwartz f n a b c d) x‖ ≤
      ‖deriv f x‖+(2*(n:ℝ)*(|a|+|c|))*‖f x‖ := by
  let m : ℝ → ℂ := fun y => (sincProductMask n (a*y+b) (c*y+d):ℂ)
  have hm : DifferentiableAt ℝ m x :=
    (sincProductAffine_hasTemperateGrowth n a b c d).1.differentiable (by simp) x
  have hd : ‖deriv m x‖ ≤ 2*(n:ℝ)*(|a|+|c|) :=
    norm_deriv_le_of_lipschitz (sincProductAffine_lipschitz n a b c d)
  have hb : ‖m x‖ ≤ 1 := by
    simpa only [m,Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonneg (sincProductMask_nonneg _ _ _)] using sincProductMask_le_one n (a*x+b) (c*x+d)
  have heq : (sincProductSchwartz f n a b c d : ℝ → ℂ) = fun y => m y*f y := by
    funext y
    exact sincProductSchwartz_apply f n a b c d y
  rw [heq]
  change ‖deriv (m*(f : ℝ → ℂ)) x‖ ≤ _
  rw [deriv_mul hm (f.differentiableAt)]
  calc
    _ ≤ ‖deriv m x‖*‖f x‖+‖m x‖*‖deriv f x‖ := by
      simpa only [norm_mul] using norm_add_le (deriv m x*f x) (m x*deriv f x)
    _ ≤ (2*(n:ℝ)*(|a|+|c|))*‖f x‖+1*‖deriv f x‖ :=
      add_le_add (mul_le_mul_of_nonneg_right hd (norm_nonneg _))
        (mul_le_mul_of_nonneg_right hb (norm_nonneg _))
    _ = _ := by ring

end LipschitzHilbert

end

end OAI
