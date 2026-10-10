import OAI.Geometry.SurfaceImmersion.Primitive.SlowPeriodicDerivative

namespace OAI

/-! Periodic integration and differentiation preserve vanishing data. -/

noncomputable section
open scoped ContDiff Topology

namespace ClosedSurfaceR4.SmoothPeriodicCalculus

open CovarianceCorrector

variable {A E : Type} [NormedAddCommGroup A] [NormedSpace ℝ A]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma derivativeFamily_zero_at (F : A → C(Period, E))
    (hF : ContDiff ℝ ∞ (fun z : A × ℝ => F z.1 (z.2 : Period)))
    {p : A} (hp : F p = 0) : derivativeFamily F hF p = 0 := by
  ext t
  refine Quotient.inductionOn' t ?_
  intro x
  have hd := derivativeFamily_hasDerivAt F hF p x
  have he : (fun s : ℝ => F p (s : Period)) = fun _ => (0 : E) := by
    funext s
    rw [hp]
    rfl
  rw [he] at hd
  exact hd.unique (hasDerivAt_const x 0)

lemma slowDerivativeFamily_zero_on (F : A → C(Period, E))
    (hF : ContDiff ℝ ∞ (fun z : A × ℝ => F z.1 (z.2 : Period)))
    {O : Set A} (hO : IsOpen O) (hz : ∀ p ∈ O, F p = 0) (v : A)
    {p : A} (hp : p ∈ O) : slowDerivativeFamily F hF v p = 0 := by
  ext t
  refine Quotient.inductionOn' t ?_
  intro x
  change slowDerivative (fun z : A × ℝ => F z.1 (z.2 : Period)) v (p, x) = 0
  rw [← fderiv_slice hF]
  change fderiv ℝ (fun q => F q (x : Period)) p v = 0
  have he : (fun q => F q (x : Period)) =ᶠ[𝓝 p] fun _ => (0 : E) := by
    filter_upwards [hO.mem_nhds hp] with q hq
    rw [hz q hq]
    rfl
  rw [he.fderiv_eq, fderiv_const_apply, zero_apply]

variable [FiniteDimensional ℝ A] [CompleteSpace E]

lemma primitiveFamily_zero_at (F : A → C(Period, E))
    (hF : ContDiff ℝ ∞ (fun z : A × ℝ => F z.1 (z.2 : Period)))
    (hm : ∀ p, (∫ t, F p t ∂AddCircle.haarAddCircle) = 0)
    {p : A} (hp : F p = 0) : primitiveFamily F hF hm p = 0 := by
  ext t
  refine Quotient.inductionOn' t ?_
  intro x
  rw [primitiveFamily_apply]
  have he : (fun s : ℝ => F p (s : Period)) = fun _ => (0 : E) := by
    funext s
    rw [hp]
    rfl
  rw [he]
  exact PeriodicPrimitive.primitive_zero x

end ClosedSurfaceR4.SmoothPeriodicCalculus

end

end OAI
