import Mathlib
import OAI.Geometry.WeakHessian.Entropy.StrongEntropyConfinement

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile64
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianTransport WeakHessianFunctional
open scoped Topology ENNReal NNReal InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X}

lemma polynomial_exp_bound {a r T : ℝ} (ha : 0 < a) (hr : 0 ≤ r) (hT : 0 ≤ T) :
    (r+T)^2*Real.exp (-(a*r)) ≤ 4/a^2+2*T^2 := by
  have hE := Real.pow_div_factorial_le_exp (a*r) (mul_nonneg ha.le hr) 2
  norm_num only [Nat.factorial, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one, mul_one, pow_two] at hE
  have hE' := mul_le_mul_of_nonneg_right hE (Real.exp_pos (-(a*r))).le
  have he : Real.exp (a*r)*Real.exp (-(a*r)) = 1 := by rw [← Real.exp_add]; simp
  rw [he] at hE'
  have hsq : r^2*Real.exp (-(a*r)) ≤ 2/a^2 := by
    apply (le_div_iff₀ (sq_pos_of_pos ha)).mpr
    nlinarith
  have hsmall : Real.exp (-(a*r)) ≤ 1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr (mul_nonneg ha.le hr))
  have hab : (r+T)^2 ≤ 2*r^2+2*T^2 := by nlinarith [sq_nonneg (r-T)]
  have H := mul_le_mul_of_nonneg_right hab (Real.exp_pos (-(a*r))).le
  have H' := mul_le_mul_of_nonneg_left hsmall (pow_nonneg hT 2)
  rw [show 4/a^2 = 2*(2/a^2) by ring]
  nlinarith

omit [ProperSpace X] in
lemma CurvatureDimension.exists_comparison_confinement {K N : ℝ} (hN : 1 < N)
    (hcd : CurvatureDimension m K N) (hfull : FullSupport m) (hfin : FiniteOnBoundedSets m) (o : X) :
    ∃ a : ℝ, 0 < a ∧
      Integrable (fun x => Real.exp (-(a*dist x o))) m ∧
      MemLp (fun x => Real.exp (-(a*dist x o))) 2 m ∧
      MemLp (fun x => (a*dist x o)*Real.exp (-(a*dist x o))) 2 m ∧
      MemLp (fun x => Real.exp (-(a*dist x o/2))) 2 m ∧
      Integrable (fun x => Real.exp (-(a*dist x o/2))) m ∧
      ∀ T : ℝ≥0, MemLp (fun x => (dist x o+T)^2*Real.exp (-(a*dist x o))) 2 m ∧
        MemLp (fun x => (dist x o+T)*Real.exp (-(a*dist x o))) 2 m := by
  obtain ⟨a,ha,hi,h2,hD,hh,hhi⟩ := hcd.exists_strong_entropy_confinement hN hfull hfin o
  have he (x : X) : Real.exp (-(2*a*dist x o)) ≤ Real.exp (-(a*dist x o)) := by
    apply Real.exp_le_exp.mpr
    nlinarith [dist_nonneg (x := x) (y := o)]
  have hi' : Integrable (fun x => Real.exp (-(2*a*dist x o))) m := hi.mono' (by fun_prop)
    (ae_of_all _ fun x => by simpa only [Real.norm_of_nonneg (Real.exp_pos _).le] using he x)
  have h2' : MemLp (fun x => Real.exp (-(2*a*dist x o))) 2 m := h2.mono (by fun_prop)
    (ae_of_all _ fun x => by simpa only [Real.norm_of_nonneg (Real.exp_pos _).le] using he x)
  have hD' : MemLp (fun x => (2*a*dist x o)*Real.exp (-(2*a*dist x o))) 2 m := by
    apply (hD.const_mul 2).mono (by fun_prop)
    exact ae_of_all _ fun x => by
      change |(2*a*dist x o)*Real.exp (-(2*a*dist x o))| ≤ |2*((a*dist x o)*Real.exp (-(a*dist x o)))|
      rw [abs_of_nonneg (by positivity),abs_of_nonneg (by positivity)]
      nlinarith [mul_le_mul_of_nonneg_left (he x) (by positivity : 0 ≤ 2*a*dist x o)]
  refine ⟨2*a,by positivity,hi',h2',hD',?_,?_,?_⟩
  · convert! h2 using 1; funext x; congr 1; ring
  · convert! hi using 1; funext x; congr 1; ring
  intro T
  have hW : MemLp (fun x => (dist x o+T)^2*Real.exp (-(2*a*dist x o))) 2 m := by
    apply (h2.const_mul (4/a^2+2*(T:ℝ)^2)).mono (by fun_prop)
    exact ae_of_all _ fun x => by
      change |(dist x o+T)^2*Real.exp (-(2*a*dist x o))| ≤ |(4/a^2+2*(T:ℝ)^2)*Real.exp (-(a*dist x o))|
      rw [abs_of_nonneg (by positivity),abs_of_nonneg (by positivity),
        show -(2*a*dist x o) = -(a*dist x o)+(-(a*dist x o)) by ring,Real.exp_add,← mul_assoc]
      exact mul_le_mul_of_nonneg_right (polynomial_exp_bound ha dist_nonneg T.coe_nonneg) (Real.exp_pos _).le
  refine ⟨hW,?_⟩
  apply (h2'.add hW).mono (by fun_prop)
  exact ae_of_all _ fun x => by
    simp only [Pi.add_apply,Real.norm_eq_abs]
    rw [abs_of_nonneg (by positivity),abs_of_nonneg (by positivity)]
    have H : dist x o+T ≤ 1+(dist x o+T)^2 := by nlinarith [sq_nonneg (dist x o+T-1/2)]
    nlinarith [mul_le_mul_of_nonneg_right H (Real.exp_pos (-(2*a*dist x o))).le]

omit [ProperSpace X] in
lemma memLp_exp_weight_of_supported (u : Lp ℝ 2 m) (o : X) {R a : ℝ}
    (ha : 0 ≤ a) (hs : ∀ᵐ x ∂m,dist x o > R → u x = 0) :
    MemLp (fun x => u x*Real.exp (a*dist x o)) 2 m := by
  apply ((Lp.memLp u).const_mul (Real.exp (a*R))).mono (by fun_prop)
  filter_upwards [hs] with x hx
  change |u x*Real.exp (a*dist x o)| ≤ |Real.exp (a*R)*u x|
  rw [abs_mul,abs_mul,abs_of_pos (Real.exp_pos _),abs_of_pos (Real.exp_pos _)]
  by_cases hR : dist x o ≤ R
  · rw [mul_comm (Real.exp (a*R))]
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hR ha)) (abs_nonneg _)
  · rw [hx (lt_of_not_ge hR)]; simp

end WeakHessian

end
end InlinedFile64

end OAI
