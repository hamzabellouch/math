import OAI.Geometry.RCD.Sobolev.LocalHessianAction

namespace OAI

/-! # The gradient-product identity in terms of actual Hessian actions

This is the finite Sobolev-representative form of Gigli's formula (3.3.33).
The identity itself is algebraic once the three Gram representatives exist.
-/

open Set Filter MeasureTheory

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)

/-- The two Hessian actions recover the derivative of the mixed Gram
representative, including an arbitrary scalar shift. -/
theorem localGamma_mixed_as_hessian_actions
    (f a z G Fz Az : SobolevSpace μ hQ) (b : ℝ) :
    localGamma μ hQ (G-b • a) z =ᵐ[μ] fun x =>
      (localHessianAction μ hQ f a z G Fz Az x-b*localGamma μ hQ a z x)+
        localHessianAction μ hQ a f z G Az Fz x := by
  filter_upwards [localGamma_sub_left μ hQ G (b • a) z,
    localGamma_smul_left μ hQ b a z,localGamma_comm μ hQ G z] with x hsub hsmul hcomm
  rw [hsub,hsmul,hcomm]
  unfold localHessianAction
  ring

private theorem diagonal_le_of_two_actions (q A B u v : ℝ) (hq : 0≤q)
    (hA : 0≤A) (hB : 0≤B)
    (he : q=u+v) (hu : u^2≤A*q) (hv : v^2≤B*q) : q≤2*(A+B) := by
  have hsq : q^2≤2*(A+B)*q := by
    calc
      q^2 = (u+v)^2 := congrArg (fun z : ℝ => z^2) he
      _ ≤ 2*(u^2+v^2) := by nlinarith only [sq_nonneg (u-v)]
      _ ≤ 2*(A*q+B*q) := mul_le_mul_of_nonneg_left (add_le_add hu hv) (by norm_num)
      _ = _ := by ring
  rcases eq_or_lt_of_le hq with hz | hp
  · rw [← hz]
    positivity
  · exact (mul_le_mul_iff_left₀ hp).mp (by simpa only [pow_two] using hsq)

/-- When the shifted mixed gradient is an admissible Hessian direction,
the two action bounds give its exact factor-two gradient estimate. -/
theorem localGamma_shifted_mixed_bound
    (f a G Fz Az : SobolevSpace μ hQ) (b : ℝ) (A B : X → ℝ)
    (hA : ∀ᵐ x ∂μ, 0≤A x) (hB : ∀ᵐ x ∂μ, 0≤B x)
    (hfirst : ∀ᵐ x ∂μ,
      (localHessianAction μ hQ f a (G-b • a) G Fz Az x-
        b*localGamma μ hQ a (G-b • a) x)^2 ≤ A x*localGamma μ hQ (G-b • a) (G-b • a) x)
    (hsecond : ∀ᵐ x ∂μ,
      (localHessianAction μ hQ a f (G-b • a) G Az Fz x)^2 ≤
        B x*localGamma μ hQ (G-b • a) (G-b • a) x) :
    ∀ᵐ x ∂μ, localGamma μ hQ (G-b • a) (G-b • a) x≤2*(A x+B x) := by
  filter_upwards [hA,hB,hfirst,hsecond,
    localGamma_mixed_as_hessian_actions μ hQ f a (G-b • a) G Fz Az b,
    localGamma_self μ hQ (G-b • a)] with x ha hb hfirst hsecond he hself
  apply diagonal_le_of_two_actions _ _ _ _ _ _ ha hb he hfirst hsecond
  rw [hself]
  positivity

end RegularPointCoordinates

end

end OAI
