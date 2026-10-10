import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousProfileSymmetries
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Normed.Module.FiniteDimension

namespace OAI

/-! # Independence of the fourteen physical modulation directions -/

open scoped ContDiff ZeroAtInfty
open Filter Topology

namespace DefocusingNLS

local notation "E" => EuclideanSpace ℝ (Fin 12)

theorem vanishing_directional_derivative_eq_zero (Q : C₀(E, ℂ))
    (hQ : Differentiable ℝ Q) (h0 : Q 0 ≠ 0) (v : E)
    (hv : ∀ y, fderiv ℝ Q y v = 0) : v = 0 := by
  by_contra hne
  have hd (t : ℝ) : HasDerivAt (fun s : ℝ => Q (s • v)) 0 t := by
    simpa only [id_eq, one_smul, hv, Function.comp_def] using!
      (hQ (t • v)).hasFDerivAt.comp_hasDerivAt t ((hasDerivAt_id t).smul_const v)
  have he : (fun t : ℝ => Q (t • v)) = fun _ => Q 0 := by
    funext t
    simpa only [zero_smul] using is_const_of_deriv_eq_zero
      (fun t => (hd t).differentiableAt) (fun t => (hd t).deriv) t 0
  have hline : Topology.IsClosedEmbedding (fun t : ℝ => t • v) :=
    isClosedEmbedding_smul_left hne
  have ht := (zero_at_infty Q).comp hline.tendsto_cocompact
  change Tendsto (fun t : ℝ => Q (t • v)) (cocompact ℝ) (𝓝 0) at ht
  rw [he] at ht
  exact h0 (tendsto_nhds_unique tendsto_const_nhds ht)

theorem even_fderiv_at_zero (Q : E → ℂ) (hQ : DifferentiableAt ℝ Q 0)
    (heven : ∀ y, Q (-y) = Q y) (v : E) : fderiv ℝ Q 0 v = 0 := by
  have he : (fun y : E => Q (-y)) = Q := funext heven
  have hd := hQ.hasFDerivAt
  have hd' : HasFDerivAt Q (fderiv ℝ Q 0) (-(0 : E)) := by simpa only [neg_zero] using hd
  have hc := hd'.comp (0 : E) ((hasFDerivAt_id (𝕜 := ℝ) (0 : E)).neg)
  change HasFDerivAt (fun y : E => Q (-y)) _ 0 at hc
  rw [he] at hc
  have hi := congrArg (fun A : E →L[ℝ] ℂ => A v) (hc.unique hd)
  simp only [ContinuousLinearMap.comp_apply, neg_apply, ContinuousLinearMap.id_apply,
    map_neg] at hi
  linear_combination - (1 / 2 : ℂ) * hi

theorem physical_symmetry_directions_independent (a b : ℝ) (ha : 0 < a)
    (Q : C₀(E, ℂ)) (hQ : Differentiable ℝ Q) (h0 : Q 0 ≠ 0)
    (heven : ∀ y, Q (-y) = Q y) (s t : ℝ) (v : E)
    (h : ∀ y, (s : ℂ) * (Complex.I * Q y) +
      (t : ℂ) * (((a : ℂ) - Complex.I * (b : ℂ)) * Q y + cartesianTransport Q y) +
        cartesianDerivative v Q y = 0) : s = 0 ∧ t = 0 ∧ v = 0 := by
  have hD : cartesianDerivative v Q 0 = 0 := even_fderiv_at_zero Q (hQ 0) heven v
  have hT : cartesianTransport Q 0 = 0 := by simp [cartesianTransport]
  have hc : (s : ℂ) * Complex.I + (t : ℂ) * ((a : ℂ) - Complex.I * (b : ℂ)) = 0 := by
    apply (mul_eq_zero.mp (show ((s : ℂ) * Complex.I +
      (t : ℂ) * ((a : ℂ) - Complex.I * (b : ℂ))) * Q 0 = 0 by
        have hz := h 0
        rw [hD, hT] at hz
        linear_combination hz)).resolve_right h0
  have hr := congrArg Complex.re hc
  simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, Complex.sub_re, Complex.sub_im, zero_mul, mul_zero,
    sub_zero, zero_sub, zero_add, Complex.zero_re] at hr
  have ht : t = 0 := (mul_eq_zero.mp hr).resolve_right ha.ne'
  have hs : s = 0 := by
    subst t
    simpa using congrArg Complex.im hc
  refine ⟨hs, ht, vanishing_directional_derivative_eq_zero Q hQ h0 v ?_⟩
  intro y
  simpa only [hs, ht, Complex.ofReal_zero, zero_mul, zero_add, cartesianDerivative] using! h y

end DefocusingNLS

end OAI
