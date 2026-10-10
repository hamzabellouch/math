import Mathlib
import OAI.Geometry.WeakHessian.LocalBounds.SquareTimePairing

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile187
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianFunctional
open scoped Topology ENNReal NNReal InnerProductSpace

variable {X : Type*} [MeasurableSpace X] {m : Measure X}
variable {Y : Type*} [TopologicalSpace Y]

lemma continuousOn_integral_square_mul {u v : Y → Lp ℝ 2 m} {S : Set Y}
    (hu : ContinuousOn u S) (hv : ContinuousOn v S) (n : ℕ)
    (hub : ∀ t ∈ S,∀ᵐ x ∂m,|u t x| ≤ (n:ℝ)) :
    ContinuousOn (fun t => ∫ x,(u t x)^2*v t x ∂m) S := by
  apply (((continuous_clipSquareLp (m := m) n).comp_continuousOn hu).inner hv).congr
  intro t ht
  dsimp only [Function.comp_def]
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [clipSquareLp_eq_square (hub t ht)] with x hx
  simp only [RCLike.inner_apply,conj_trivial,hx]
  ring

lemma continuousOn_integral_mul_mul {u v w : Y → Lp ℝ 2 m} {S : Set Y}
    (hu : ContinuousOn u S) (hv : ContinuousOn v S) (hw : ContinuousOn w S)
    (n : ℕ) (hub : ∀ t ∈ S,∀ᵐ x ∂m,|u t x| ≤ (n:ℝ))
    (hvb : ∀ t ∈ S,∀ᵐ x ∂m,|v t x| ≤ (n:ℝ)) :
    ContinuousOn (fun t => ∫ x,u t x*v t x*w t x ∂m) S := by
  have hs : ∀ t ∈ S,∀ᵐ x ∂m,|(u t+v t) x| ≤ ((2*n:ℕ):ℝ) := by
    intro t ht
    filter_upwards [hub t ht,hvb t ht,Lp.coeFn_add (u t) (v t)] with x hx hy he
    rw [he]; push_cast
    exact (abs_add_le _ _).trans (by linarith)
  have hc := (((continuousOn_integral_square_mul (hu.add hv) hw (2*n) hs).sub
    (continuousOn_integral_square_mul hu hw n hub)).sub
    (continuousOn_integral_square_mul hv hw n hvb)).div_const 2
  apply hc.congr
  intro t ht
  have iu : Integrable (fun x => (u t x)^2*w t x) m := by
    have H := (memLp_mul_bounded (Lp.memLp (u t)) (Lp.aestronglyMeasurable (u t)) (hub t ht)).integrable_mul (Lp.memLp (w t))
    change Integrable (fun x => u t x*u t x*w t x) m at H
    simpa only [pow_two] using H
  have iv : Integrable (fun x => (v t x)^2*w t x) m := by
    have H := (memLp_mul_bounded (Lp.memLp (v t)) (Lp.aestronglyMeasurable (v t)) (hvb t ht)).integrable_mul (Lp.memLp (w t))
    change Integrable (fun x => v t x*v t x*w t x) m at H
    simpa only [pow_two] using H
  have iuv : Integrable (fun x => u t x*v t x*w t x) m :=
    (memLp_mul_bounded (Lp.memLp (u t)) (Lp.aestronglyMeasurable (v t)) (hvb t ht)).integrable_mul (Lp.memLp (w t))
  have he : (∫ x,((u t+v t) x)^2*w t x ∂m) =
      (∫ x,(u t x)^2*w t x ∂m)+2*(∫ x,u t x*v t x*w t x ∂m)+
      (∫ x,(v t x)^2*w t x ∂m) := by
    calc
      _ = ∫ x,((u t x)^2*w t x+2*(u t x*v t x*w t x))+(v t x)^2*w t x ∂m := by
        apply integral_congr_ae
        filter_upwards [Lp.coeFn_add (u t) (v t)] with x hx
        rw [hx]; simp only [Pi.add_apply]; ring
      _ = _ := by
        rw [integral_add (f := fun x => (u t x)^2*w t x+2*(u t x*v t x*w t x))
          (iu.add (iuv.const_mul 2)) iv,integral_add iu (iuv.const_mul 2),integral_const_mul]
  dsimp only [Pi.div_apply,Pi.sub_apply,Pi.add_apply]
  rw [he]
  ring
end WeakHessian

end
end InlinedFile187

end OAI
