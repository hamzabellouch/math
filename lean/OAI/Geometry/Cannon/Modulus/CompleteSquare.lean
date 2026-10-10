import Mathlib
import OAI.Geometry.Cannon.Modulus.Quad

namespace OAI

section
noncomputable section
namespace CannonGeneralizedDisk
open Set Metric
open scoped ComplexConjugate OnePoint

lemma Quad.complete_square (q : Quad) (hA : q.A≠0) (z : ℂ) :
    q.value z=q.A*(dist z (q.b/(q.A:ℂ))^2-q.discr/q.A^2) := by
  rw [dist_eq_norm,←Complex.normSq_eq_norm_sq]
  simp only [value,discr,Complex.normSq_apply,Complex.sub_re,Complex.sub_im,
    Complex.div_ofReal_re,Complex.div_ofReal_im,Complex.mul_re,
    Complex.conj_re,Complex.conj_im]
  field_simp
  ring

lemma Quad.finite_disk (q : Quad) (hA : 0<q.A) (hq : 0<q.discr) :
    ∃ a : ℂ,∃ r : ℝ,0<r ∧ q.region=((↑) '' ball a r : Set (OnePoint ℂ)) := by
  let a : ℂ:=q.b/(q.A:ℂ)
  let r : ℝ:=Real.sqrt q.discr/q.A
  have hr : 0<r:=div_pos (Real.sqrt_pos.mpr hq) hA
  have hr2 : r^2=q.discr/q.A^2:=by
    dsimp [r]
    rw [div_pow,Real.sq_sqrt hq.le]
  refine ⟨a,r,hr,?_⟩
  ext p
  induction p using OnePoint.rec with
  | infty => simp [Quad.region,not_lt.mpr hA.le]
  | coe z =>
    rw [Quad.mem_region_coe,q.complete_square hA.ne' z,←hr2]
    change q.A*(dist z a^2-r^2)<0 ↔ (z:OnePoint ℂ)∈(↑) '' ball a r
    have hm : q.A*(dist z a^2-r^2)<0 ↔ dist z a^2-r^2<0 := by
      simpa only [mul_zero] using
        (mul_lt_mul_iff_right₀ hA : q.A*(dist z a^2-r^2)<q.A*0 ↔ dist z a^2-r^2<0)
    rw [hm]
    constructor
    · intro h
      refine ⟨z,mem_ball.mpr ?_,rfl⟩
      nlinarith [dist_nonneg (x:=z) (y:=a)]
    · rintro ⟨w,hw,he⟩
      have he' : w=z:=OnePoint.coe_injective he
      subst w
      have hd:=mem_ball.mp hw
      nlinarith [dist_nonneg (x:=z) (y:=a)]

end CannonGeneralizedDisk

end
end

end OAI
