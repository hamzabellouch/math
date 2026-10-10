import Mathlib
import OAI.Geometry.WeakHessian.Sobolev.BochnerConvex

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianFunctional
open scoped Topology ENNReal NNReal InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X]
variable {m : Measure X} [SigmaFinite m]

omit [ProperSpace X] [SigmaFinite m] in
lemma WeakHessianUpperBound.mono_bounded (hfin : FiniteOnBoundedSets m)
    {F G H : X → ℝ} (h : WeakHessianUpperBound m F G)
    (hGm : AEStronglyMeasurable G m) (hHm : AEStronglyMeasurable H m)
    {CG CH : ℝ} (hGb : ∀ x, |G x| ≤ CG) (hHb : ∀ x, |H x| ≤ CH)
    (hGH : ∀ x, G x ≤ H x) : WeakHessianUpperBound m F H := by
  intro g hg hgs φ hφ hφs hφn
  obtain ⟨L,hL⟩ := hg.1
  obtain ⟨Lφ,hLφ⟩ := hφ
  obtain ⟨B,hB⟩ := hφs.exists_bound_of_continuous hLφ.continuous
  have hφb (x : X) : |φ x| ≤ max B 0 := by
    exact (show |φ x| ≤ B by simpa only [Real.norm_eq_abs] using hB x).trans (le_max_left _ _)
  have hi (J : X → ℝ) (hJm : AEStronglyMeasurable J m) {C : ℝ}
      (hJb : ∀ x, |J x| ≤ C) : Integrable (fun x => φ x*J x*gamma m g g x) m := by
    apply integrable_bounded_gamma hfin hL.1 hL.1 (hLφ.continuous.aestronglyMeasurable.mul hJm)
      (C := max B 0*max C 0)
    exact ae_of_all _ fun x => by
      rw [Pi.mul_apply,abs_mul]
      exact mul_le_mul (hφb x) ((hJb x).trans (le_max_left _ _)) (abs_nonneg _) (le_max_right _ _)
  apply (h g hg hgs φ ⟨Lφ,hLφ⟩ hφs hφn).trans
  apply integral_mono_ae (hi G hGm hGb) (hi H hHm hHb)
  filter_upwards [gamma_self (m := m) g] with x hx
  rw [hx]
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hGH x) (hφn x)) (sq_nonneg _)

lemma abs_max_le_of_abs_le {x B c : ℝ} (hx : |x| ≤ B) : |max x c| ≤ B+|c| := by
  apply abs_le.mpr
  constructor
  · have H := (abs_le.mp hx).1
    linarith [le_max_left x c,abs_nonneg c]
  · exact max_le (by linarith [(abs_le.mp hx).2,abs_nonneg c])
      (by linarith [le_abs_self c,(abs_nonneg x).trans hx])

end WeakHessian

end
end

end OAI
