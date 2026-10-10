import Mathlib
import OAI.Geometry.WeakHessian.LocalBounds.SquareTimePairing

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile186
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianFunctional
open scoped Topology ENNReal NNReal InnerProductSpace

variable {X : Type*} [MeasurableSpace X] {m : Measure X}

lemma integral_bounded_triple (u v w : Lp ℝ 2 m) {B : ℝ}
    (hw : ∀ᵐ x ∂m,|w x| ≤ B) : Integrable (fun x => u x*v x*w x) m := by
  simpa only [Pi.mul_apply,mul_comm (w _)] using
    (Lp.memLp u |>.integrable_mul (Lp.memLp v)).bdd_mul (Lp.aestronglyMeasurable w)
      (by simpa only [Real.norm_eq_abs] using hw)

lemma hasDerivAt_integral_mul_mul {u v w : ℝ → Lp ℝ 2 m}
    {u' v' w' : Lp ℝ 2 m} {a : ℝ}
    (hu : HasDerivAt u u' a) (hv : HasDerivAt v v' a) (hw : HasDerivAt w w' a)
    (n : ℕ) (hub : ∀ᶠ t in 𝓝 a,∀ᵐ x ∂m,|u t x| ≤ (n:ℝ))
    (hvb : ∀ᶠ t in 𝓝 a,∀ᵐ x ∂m,|v t x| ≤ (n:ℝ))
    {B : ℝ} (hwb : ∀ᵐ x ∂m,|w a x| ≤ B) :
    HasDerivAt (fun t => ∫ x,u t x*v t x*w t x ∂m)
      ((∫ x,u' x*v a x*w a x ∂m)+(∫ x,u a x*v' x*w a x ∂m)+
        (∫ x,u a x*v a x*w' x ∂m)) a := by
  have huba := mem_of_mem_nhds hub
  have hvba := mem_of_mem_nhds hvb
  have hs : ∀ᶠ t in 𝓝 a,∀ᵐ x ∂m,|(u t+v t) x| ≤ ((2*n:ℕ):ℝ) := by
    filter_upwards [hub,hvb] with t ht hv
    filter_upwards [ht,hv,Lp.coeFn_add (u t) (v t)] with x hx hy he
    rw [he]
    push_cast
    exact (abs_add_le _ _).trans (by linarith)
  have hd := ((hasDerivAt_integral_square_mul (hu.add hv) hw (2*n) hs hwb).sub
    (hasDerivAt_integral_square_mul hu hw n hub hwb)).sub
      (hasDerivAt_integral_square_mul hv hw n hvb hwb)
  have hi (t : ℝ) (ht : ∀ᵐ x ∂m,|u t x| ≤ (n:ℝ))
      (hv : ∀ᵐ x ∂m,|v t x| ≤ (n:ℝ)) :
      (∫ x,((u t+v t) x)^2*w t x ∂m)-(∫ x,(u t x)^2*w t x ∂m)-
        (∫ x,(v t x)^2*w t x ∂m) = 2*(∫ x,u t x*v t x*w t x ∂m) := by
    have iu := (memLp_mul_bounded (Lp.memLp (u t)) (Lp.aestronglyMeasurable (u t)) ht).integrable_mul (Lp.memLp (w t))
    have iv := (memLp_mul_bounded (Lp.memLp (v t)) (Lp.aestronglyMeasurable (v t)) hv).integrable_mul (Lp.memLp (w t))
    have iuv := (memLp_mul_bounded (Lp.memLp (u t)) (Lp.aestronglyMeasurable (v t)) hv).integrable_mul (Lp.memLp (w t))
    change Integrable (fun x => u t x*u t x*w t x) m at iu
    change Integrable (fun x => v t x*v t x*w t x) m at iv
    change Integrable (fun x => u t x*v t x*w t x) m at iuv
    have he : (∫ x,((u t+v t) x)^2*w t x ∂m) =
      (∫ x,(u t x)^2*w t x ∂m)+2*(∫ x,u t x*v t x*w t x ∂m)+
        (∫ x,(v t x)^2*w t x ∂m) := by
      calc
        _ = ∫ x,((u t x)^2*w t x+2*(u t x*v t x*w t x))+(v t x)^2*w t x ∂m := by
          apply integral_congr_ae
          filter_upwards [Lp.coeFn_add (u t) (v t)] with x hx
          rw [hx]; simp only [Pi.add_apply]; ring
        _ = _ := by
          have iu' : Integrable (fun x => (u t x)^2*w t x) m := by simpa only [pow_two] using iu
          have iv' : Integrable (fun x => (v t x)^2*w t x) m := by simpa only [pow_two] using iv
          rw [integral_add (f := fun x => (u t x)^2*w t x+2*(u t x*v t x*w t x)) (iu'.add (iuv.const_mul 2)) iv',
            integral_add iu' (iuv.const_mul 2),integral_const_mul]
    linarith
  have heq : (fun t => (∫ x,((u t+v t) x)^2*w t x ∂m)-(∫ x,(u t x)^2*w t x ∂m)-
        (∫ x,(v t x)^2*w t x ∂m)) =ᶠ[𝓝 a]
      (fun t => 2*(∫ x,u t x*v t x*w t x ∂m)) := by
    filter_upwards [hub,hvb] with t ht hv
    exact hi t ht hv
  have hd' := (hd.congr_of_eventuallyEq heq.symm).div_const 2

  have hab : Integrable (fun x => u a x*v a x*w' x) m :=
    (memLp_mul_bounded (Lp.memLp (u a)) (Lp.aestronglyMeasurable (v a)) hvba).integrable_mul (Lp.memLp w')
  have hsq (p : Lp ℝ 2 m) (hp : ∀ᵐ x ∂m,|p x| ≤ (n:ℝ)) :
      Integrable (fun x => (p x)^2*w' x) m := by
    have H := (memLp_mul_bounded (Lp.memLp p) (Lp.aestronglyMeasurable p) hp).integrable_mul (Lp.memLp w')
    change Integrable (fun x => p x*p x*w' x) m at H
    simpa only [pow_two] using H
  have e1 : (∫ x,(u a+v a) x*(u'+v') x*w a x ∂m) =
      (∫ x,u a x*u' x*w a x ∂m)+(∫ x,u a x*v' x*w a x ∂m)+
      (∫ x,u' x*v a x*w a x ∂m)+(∫ x,v a x*v' x*w a x ∂m) := by
    calc
      _ = ∫ x,((u a x*u' x*w a x+u a x*v' x*w a x)+u' x*v a x*w a x)+v a x*v' x*w a x ∂m := by
        apply integral_congr_ae
        filter_upwards [Lp.coeFn_add (u a) (v a),Lp.coeFn_add u' v'] with x hx hy
        rw [hx,hy]; simp only [Pi.add_apply]; ring
      _ = _ := by
        have i1 := integral_bounded_triple (u a) u' (w a) hwb
        have i2 := integral_bounded_triple (u a) v' (w a) hwb
        have i3 := integral_bounded_triple u' (v a) (w a) hwb
        have i4 := integral_bounded_triple (v a) v' (w a) hwb
        rw [integral_add (f := fun x => (u a x*u' x*w a x+u a x*v' x*w a x)+u' x*v a x*w a x) ((i1.add i2).add i3) i4,
          integral_add (f := fun x => u a x*u' x*w a x+u a x*v' x*w a x) (i1.add i2) i3,integral_add i1 i2]
  have e2 : (∫ x,((u a+v a) x)^2*w' x ∂m) =
      (∫ x,(u a x)^2*w' x ∂m)+2*(∫ x,u a x*v a x*w' x ∂m)+
        (∫ x,(v a x)^2*w' x ∂m) := by
    calc
      _ = ∫ x,((u a x)^2*w' x+2*(u a x*v a x*w' x))+(v a x)^2*w' x ∂m := by
        apply integral_congr_ae
        filter_upwards [Lp.coeFn_add (u a) (v a)] with x hx
        rw [hx]; simp only [Pi.add_apply]; ring
      _ = _ := by
        rw [integral_add (f := fun x => (u a x)^2*w' x+2*(u a x*v a x*w' x)) ((hsq _ huba).add (hab.const_mul 2)) (hsq _ hvba),
          integral_add (hsq _ huba) (hab.const_mul 2),integral_const_mul]
  simp only [Pi.add_apply] at hd'
  rw [e1,e2] at hd'
  convert! hd' using 1 <;> (first | (funext t; ring) | ring)
end WeakHessian

end
end InlinedFile186

end OAI
