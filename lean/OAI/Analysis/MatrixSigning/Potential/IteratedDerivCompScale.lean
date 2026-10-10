import Mathlib
import OAI.Analysis.MatrixSigning.Potential.LineShiftIteratedDeriv

namespace OAI

open Matrix

namespace CurrentKS.Difference

section

lemma iteratedDeriv_comp_scale (n : ℕ) (f : ℝ → ℝ) (a c : ℝ) :
    iteratedDeriv n (fun x => f (c*x)) a = c^n*iteratedDeriv n f (c*a) := by
  induction n generalizing a with
  | zero => simp only [iteratedDeriv_zero,pow_zero,one_mul]
  | succ n ih =>
    have he : iteratedDeriv n (fun x => f (c*x)) = fun x => c^n*iteratedDeriv n f (c*x) := funext ih
    rw [iteratedDeriv_succ,iteratedDeriv_succ,he]
    rw [show (fun x => c^n*iteratedDeriv n f (c*x)) =
      (fun x => (fun y => c^n*iteratedDeriv n f y) (c*x)) from rfl]
    rw [deriv_comp_mul_left c (fun y => c^n*iteratedDeriv n f y) a,deriv_const_mul_field,smul_eq_mul,pow_succ]
    ring

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
lemma line_derivative_scale (n : ℕ) (f : E → ℝ) (x h : E) (c : ℝ) :
    iteratedDeriv n (fun t : ℝ => f (x+t • (c • h))) 0 =
      c^n*iteratedDeriv n (fun t : ℝ => f (x+t • h)) 0 := by
  have he : (fun t : ℝ => f (x+t • (c • h))) =
      (fun t : ℝ => (fun r : ℝ => f (x+r • h)) (c*t)) := by
    ext t
    rw [smul_smul,mul_comm]
  rw [he,iteratedDeriv_comp_scale n (fun r : ℝ => f (x+r • h)) 0 c,mul_zero]

lemma bounded_directional_derivative (n : ℕ) (f : E → ℝ) (x h : E) {s M : ℝ}
    (hs : 0 < s) (hh : ‖h‖ ≤ s)
    (hM : ∀ u : E, ‖u‖ ≤ 1 → |iteratedDeriv n (fun t : ℝ => f (x+t • u)) 0| ≤ M) :
    |iteratedDeriv n (fun t : ℝ => f (x+t • h)) 0| ≤ M*s^n := by
  have hu : ‖s⁻¹ • h‖ ≤ 1 := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hs)]
    calc
      _ ≤ s⁻¹*s := mul_le_mul_of_nonneg_left hh (inv_nonneg.mpr hs.le)
      _ = 1 := inv_mul_cancel₀ hs.ne'
  have he : h=s • (s⁻¹ • h) := by rw [smul_smul,mul_inv_cancel₀ hs.ne',one_smul]
  conv_lhs => rw [he,line_derivative_scale,abs_mul,abs_pow,abs_of_pos hs]
  simpa only [mul_comm] using mul_le_mul_of_nonneg_left (hM _ hu) (pow_nonneg hs.le n)

end

section
open Set
open scoped ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma segment_in_ball {x v : E} {s k t : ℝ} (hs : 0 ≤ s) (hk : 0 ≤ k)
    (hv : ‖v‖ ≤ k) (ht : t ∈ Icc 0 s) : ‖(x+t • v)-x‖ ≤ k*s := by
  rw [add_sub_cancel_left,norm_smul,Real.norm_eq_abs,abs_of_nonneg ht.1]
  calc
    t*‖v‖ ≤ t*k := mul_le_mul_of_nonneg_left hv ht.1
    _ ≤ s*k := mul_le_mul ht.2 le_rfl hk hs
    _ = k*s := mul_comm _ _

theorem ball_quadratic_remainder (f : E → ℝ) (x v : E) {s k M : ℝ}
    (hs : 0 < s) (hk : 0 < k) (hv : ‖v‖ ≤ k)
    (hf : ∀ y,‖y-x‖ ≤ k*s → ContDiffAt ℝ 3 f y)
    (hM : ∀ y,‖y-x‖ ≤ k*s → ∀ u,‖u‖ ≤ 1 →
      |iteratedDeriv 3 (fun t : ℝ => f (y+t • u)) 0| ≤ M) :
    |f (x+s • v)-(f x+s*(fderiv ℝ f x v)+
      s^2/2*(fderiv ℝ (fderiv ℝ f) x v v))| ≤ (M*k^3)*s^3/6 := by
  apply line_quadratic_remainder hs
  · exact fun t ht => hf _ (segment_in_ball hs.le hk.le hv ht)
  · intro t ht
    exact bounded_directional_derivative 3 f (x+t • v) v hk hv
      (hM _ (segment_in_ball hs.le hk.le hv ⟨ht.1.le,ht.2.le⟩))

end

open scoped BigOperators

lemma quadratic_entrywise_error {N : ℕ} (E : Matrix (Fin N) (Fin N) ℝ) (x : EuclideanSpace ℝ (Fin N))
    {b : ℝ} (hb : 0 ≤ b) (he : ∀ i j,|E i j| ≤ b) :
    |∑ i,∑ j, E i j*x i*x j| ≤ (N:ℝ)*b*‖x‖^2 := by
  have h1 : |∑ i,∑ j, E i j*x i*x j| ≤ ∑ i,∑ j,b * |x i| * |x j| := by
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    apply Finset.sum_le_sum
    intro i _
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    apply Finset.sum_le_sum
    intro j _
    simp only [abs_mul]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (he i j) (abs_nonneg _)) (abs_nonneg _)
  have h2 : (∑ i : Fin N, |x i|)^2 ≤ (N:ℝ)*‖x‖^2 := by
    have h := sq_sum_le_card_mul_sum_sq (s:=Finset.univ) (f:=fun i : Fin N => |x i|)
    simpa only [Finset.card_univ,Fintype.card_fin,sq_abs,EuclideanSpace.real_norm_sq_eq] using h
  apply h1.trans
  have heq : (∑ i,∑ j,b * |x i| * |x j|) = b*(∑ i : Fin N,|x i|)^2 := by
    simp only [pow_two,Finset.mul_sum,Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [heq]
  nlinarith [mul_le_mul_of_nonneg_left h2 hb]

lemma mixed_error {fpp fpm fmp fmm f0 gi gj Hi Hj Hij h R e vpp vpm vmp vmm : ℝ}
    (hh : 0 < h)
    (hpp : |fpp-(f0+h*(gi+gj)+h^2/2*(Hi+Hj+2*Hij))| ≤ R)
    (hpm : |fpm-(f0+h*(gi-gj)+h^2/2*(Hi+Hj-2*Hij))| ≤ R)
    (hmp : |fmp-(f0+h*(-gi+gj)+h^2/2*(Hi+Hj-2*Hij))| ≤ R)
    (hmm : |fmm-(f0+h*(-gi-gj)+h^2/2*(Hi+Hj+2*Hij))| ≤ R)
    (vpp' : |vpp-fpp| ≤ e) (vpm' : |vpm-fpm| ≤ e)
    (vmp' : |vmp-fmp| ≤ e) (vmm' : |vmm-fmm| ≤ e) :
    |(vpp-vpm-vmp+vmm)/(4*h^2)-Hij| ≤ (R+e)/h^2 := by
  have hpp' := abs_le.mp hpp
  have hpm' := abs_le.mp hpm
  have hmp' := abs_le.mp hmp
  have hmm' := abs_le.mp hmm
  have vpp'' := abs_le.mp vpp'
  have vpm'' := abs_le.mp vpm'
  have vmp'' := abs_le.mp vmp'
  have vmm'' := abs_le.mp vmm'
  have ha : |vpp-vpm-vmp+vmm-4*h^2*Hij| ≤ 4*(R+e) := by
    rw [abs_le]
    constructor <;> linarith
  have heq : (vpp-vpm-vmp+vmm)/(4*h^2)-Hij =
      (vpp-vpm-vmp+vmm-4*h^2*Hij)/(4*h^2) := by field_simp
  rw [heq,abs_div,abs_of_pos (by positivity : (0:ℝ)<4*h^2)]
  apply (div_le_iff₀ (by positivity : (0:ℝ)<4*h^2)).mpr
  calc
    _ ≤ 4*(R+e) := ha
    _ = (R+e)/h^2*(4*h^2) := by field_simp

end CurrentKS.Difference

end OAI
