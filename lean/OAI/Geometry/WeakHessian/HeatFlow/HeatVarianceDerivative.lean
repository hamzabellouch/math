import Mathlib
import OAI.Geometry.WeakHessian.HeatFlow.HeatPositiveDerivative
import OAI.Geometry.WeakHessian.HeatFlow.SquareGeneratorPairing
import OAI.Geometry.WeakHessian.LocalBounds.SquareTimePairing

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile134
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianFunctional
open scoped Topology ENNReal NNReal InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X} [SigmaFinite m]

omit [CompleteSpace X] in
lemma RCD.cheegerHeat_variance_derivative {K N : ℝ} (hN : 1 < N)
    (hrcd : RCD m K N) (hfull : FullSupport m) (hfin : FiniteOnBoundedSets m)
    (h : QuadraticCheegerEnergy m) (o : X) {f : X → ℝ} {L : ℝ≥0}
    (hf : LipschitzWith L f) (hf2 : MemLp f 2 m) (n : ℕ) (hfb : ∀ x,|f x| ≤ (n:ℝ))
    (ρ : Lp ℝ 2 m) {C : ℝ} (hC : 0 ≤ C) (hρb : ∀ᵐ x ∂m,|ρ x| ≤ C)
    {t s : ℝ} (hs : 0 < s) (hst : s < t) :
    HasDerivAt (fun r => ∫ x,(cheegerHeat h r (hf2.toLp f) x)^2*cheegerHeat h (t-r) ρ x ∂m)
      (-2*(∫ x,cheegerHeat h (t-s) ρ x*(weakGradient m (cheegerHeat h s (hf2.toLp f) : X → ℝ) x)^2 ∂m)) s := by
  let u := hf2.toLp f
  have huB : ∀ᵐ x ∂m,|u x| ≤ (n:ℝ) := by
    filter_upwards [hf2.coeFn_toLp] with x hx
    rw [show u x=f x from hx]
    exact hfb x
  obtain ⟨A,hA,hdA⟩ := cheegerHeat_deriv_at_positive hfin h u hs
  obtain ⟨B,hB,hdB⟩ := cheegerHeat_deriv_at_positive hfin h ρ (sub_pos.mpr hst)
  have hdρ : HasDerivAt (fun r => cheegerHeat h (t-r) ρ) (-B) s := by
    have HH := hdB.scomp s ((hasDerivAt_const s t).sub (hasDerivAt_id s))
    simpa only [Function.comp_def,id_eq,zero_sub,neg_smul,one_smul] using HH
  have hvB := cheegerHeat_bounded h (sub_pos.mpr hst).le hC ρ hρb
  have HD := hasDerivAt_integral_square_mul hdA hdρ n
    (show ∀ᶠ r in 𝓝 s,∀ᵐ x ∂m,|cheegerHeat h r u x| ≤ (n:ℝ) from by
      filter_upwards [eventually_gt_nhds hs] with r hr
      exact cheegerHeat_bounded h hr.le (Nat.cast_nonneg n) u huB) hvB
  obtain ⟨g,hg,hge⟩ := hrcd.cheegerHeat_lipschitzVersion hN hfull hfin h hf hf2 hfb hs.le
  have hgB : ∀ x,|g x| ≤ (n:ℝ) := continuous_le_of_ae_le hfull hg.continuous.abs continuous_const (by
    filter_upwards [hge,cheegerHeat_bounded h hs.le (Nat.cast_nonneg n) u huB] with x hx hb
    rwa [hx])
  have hgl : IsLaplacian m g A :=
    (hrcd.1.global_isLaplacian_of_formGenerator hfin o h _ _ hA).congr_ae hge.symm Filter.EventuallyEq.rfl
  have hvl := hrcd.1.global_isLaplacian_of_formGenerator hfin o h _ _ hB
  have H := hgl.square_pairing hfin (hrcd.1.global_localGradientParallelogram hfin o hrcd.2) hvl hg hgB hvB
  have he1 : (∫ x,g x*A x*cheegerHeat h (t-s) ρ x ∂m) =
      ∫ x,cheegerHeat h s u x*A x*cheegerHeat h (t-s) ρ x ∂m := by
    apply integral_congr_ae
    filter_upwards [hge] with x hx
    rw [hx]
  have he2 : (∫ x,(g x)^2*B x ∂m) = ∫ x,(cheegerHeat h s u x)^2*B x ∂m := by
    apply integral_congr_ae
    filter_upwards [hge] with x hx
    rw [hx]
  have he3 : (∫ x,cheegerHeat h (t-s) ρ x*(weakGradient m g x)^2 ∂m) =
      ∫ x,cheegerHeat h (t-s) ρ x*(weakGradient m (cheegerHeat h s u : X → ℝ) x)^2 ∂m := by
    apply integral_congr_ae
    filter_upwards [weakGradient_congr_ae hge] with x hx
    rw [hx]
  rw [he1,he2,he3] at H
  have he4 : (∫ x,(cheegerHeat h s u x)^2*(-B) x ∂m) = -(∫ x,(cheegerHeat h s u x)^2*B x ∂m) := by
    rw [← integral_neg]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_neg B] with x hx
    rw [hx]
    simp only [Pi.neg_apply,mul_neg]
  rw [he4,← sub_eq_add_neg,H] at HD
  exact HD
end WeakHessian

end
end InlinedFile134

end OAI
