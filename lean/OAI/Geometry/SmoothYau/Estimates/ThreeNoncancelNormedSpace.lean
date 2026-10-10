import Mathlib
import OAI.Geometry.SmoothYau.Geometry.ThreeDirectionsNormedSpace

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set Filter Function
open scoped Topology ContDiff
lemma complex_coefficient_norm_le (C D : ℂ) :
    ‖C‖ ≤ |(C+D).re|+|C.im|+‖D‖ := by
  have hh : |C.re| ≤ |(C+D).re|+|D.re| := by
    have h := abs_sub_le (C+D).re 0 D.re
    simpa only [Complex.add_re,add_sub_cancel_right,sub_zero,zero_sub,abs_neg] using h
  have hd := Complex.abs_re_le_norm D
  have hc := Complex.norm_le_abs_re_add_abs_im C
  linarith
lemma coupled_power_comparison {x y r : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hr : 0 ≤ r) (hr1 : r ≤ 1) {k : ℕ} (hk : 2 ≤ k)
    (h : x^(k-1) ≤ 2*r^k*y^(k-1)) : x^k ≤ 4*r*r^k*y^k := by
  have hpow (z : ℝ) : z^(k-1)*z=z^k := by rw [← pow_succ,Nat.sub_add_cancel (by omega)]
  have htwo : (2:ℝ) ≤ 2^(k-1) := by
    simpa using (pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) (by omega : 1 ≤ k-1))
  have hcoef : 2*r^k ≤ (2*r)^(k-1) := by
    rw [mul_pow]
    calc
      _ = (2*r)*r^(k-1) := by rw [← hpow r]; ring
      _ ≤ 2^(k-1)*r^(k-1) := mul_le_mul_of_nonneg_right (by nlinarith) (pow_nonneg hr _)
  have hxy : x ≤ 2*r*y := by
    apply le_of_pow_le_pow_left₀ (by omega : k-1≠0) (by positivity)
    rw [mul_pow]
    exact h.trans (mul_le_mul_of_nonneg_right hcoef (pow_nonneg hy _))
  calc
    _ = x*x^(k-1) := by rw [mul_comm,hpow]
    _ ≤ (2*r*y)*(2*r^k*y^(k-1)) := mul_le_mul hxy h (pow_nonneg hx _) (by positivity)
    _ = 4*r*r^k*y^k := by rw [← hpow y]; ring

lemma coupled_power_uniform_bound {A B w : ℂ} {r : ℝ} (hr : 0 < r) (hr8 : r ≤ 1/8)
    (hA : ‖A‖ ≤ 1) (hB : ‖B‖ ≤ 1) (hw : ‖w‖=1) {k : ℕ} (hk : 2 ≤ k) :
    ‖A‖^k+r^k*‖B‖^k ≤ 3*(‖A^k+(r:ℂ)^k*B^k‖+
      |(w*A^(k-1)+w*(r:ℂ)^k*B^(k-1)).re|+
      |(w*A^(k-1)).im|+|(w*(r:ℂ)^k*B^(k-1)).im|) := by
  let C := w*A^(k-1)
  let D := w*(r:ℂ)^k*B^(k-1)
  have hC : ‖C‖=‖A‖^(k-1) := by simp [C,norm_pow,hw]
  have hD : ‖D‖=r^k*‖B‖^(k-1) := by simp [D,norm_pow,hw,Complex.norm_real,abs_of_pos hr]
  have hpow (z : ℝ) : z^(k-1)*z=z^k := by rw [← pow_succ,Nat.sub_add_cancel (by omega)]
  by_cases hsmall : ‖D‖ ≤ ‖C‖/2
  · have hca := complex_coefficient_norm_le C D
    have hW : ‖A‖^k+r^k*‖B‖^k ≤ ‖C‖+‖D‖ := by
      rw [hC,hD]
      apply add_le_add
      · rw [← hpow ‖A‖]
        exact mul_le_of_le_one_right (pow_nonneg (norm_nonneg A) _) hA
      · apply mul_le_mul_of_nonneg_left _ (pow_nonneg hr.le k)
        rw [← hpow ‖B‖]
        exact mul_le_of_le_one_right (pow_nonneg (norm_nonneg B) _) hB
    change ‖A‖^k+r^k*‖B‖^k ≤ 3*(‖A^k+(r:ℂ)^k*B^k‖+|(C+D).re|+|C.im|+|D.im|)
    nlinarith [norm_nonneg (A^k+(r:ℂ)^k*B^k),abs_nonneg D.im]
  · have hcomp : ‖A‖^(k-1) ≤ 2*r^k*‖B‖^(k-1) := by rw [←hC,mul_assoc,←hD]; linarith
    have hbig := coupled_power_comparison (norm_nonneg A) (norm_nonneg B) hr.le
      (by linarith : r≤1) hk hcomp
    have hF : r^k*‖B‖^k-‖A‖^k ≤ ‖A^k+(r:ℂ)^k*B^k‖ := by
      have hh := norm_sub_norm_le ((r:ℂ)^k*B^k) (-A^k)
      simpa only [sub_neg_eq_add,add_comm,norm_neg,norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,
        abs_of_pos hr] using hh
    have hquarter : ‖A‖^k ≤ (r^k*‖B‖^k)/2 := by
      have hn : 0 ≤ r^k*‖B‖^k := by positivity
      nlinarith
    have hn1 := abs_nonneg (w*A^(k-1)+w*(r:ℂ)^k*B^(k-1)).re
    have hn2 := abs_nonneg (w*A^(k-1)).im
    have hn3 := abs_nonneg (w*(r:ℂ)^k*B^(k-1)).im
    nlinarith
end


open Set Filter Function Manifold Module
open scoped Topology ContDiff InnerProductSpace Matrix
local instance threeNoncancelNormedSpace : NormedSpace ℝ ThreeModel := inferInstance
local instance threeNoncancelContinuousSMul : ContinuousSMul ℝ ThreeModel := IsBoundedSMul.continuousSMul
local instance threeNoncancel_dimension_fact (n : ℕ) : Fact (Module.finrank ℝ (Euclidean (n+1))=n+1) := ⟨by simp [Euclidean]⟩
lemma productSphere_norm_sq (p : Sphere 2) : (p:Euclidean 3) 0^2+(p:Euclidean 3) 1^2+(p:Euclidean 3) 2^2=1 := by
  have hn : ‖(p:Euclidean 3)‖=1 := by simpa only [Metric.mem_sphere,dist_zero_right] using p.property
  have hh := PiLp.norm_sq_eq_of_L2 (fun _ : Fin 3 => ℝ) (p:Euclidean 3)
  simpa [hn,Fin.sum_univ_succ,Real.norm_eq_abs,sq_abs,add_assoc] using hh.symm
lemma productA_norm_le (p : Sphere 2) : ‖productA p‖≤1 := by
  have hh := productSphere_norm_sq p
  have hn := Complex.normSq_eq_norm_sq (productA p)
  simp only [Complex.normSq_apply,productA_re,productA_im] at hn
  nlinarith [sq_nonneg ((p:Euclidean 3) 2),norm_nonneg (productA p)]
lemma productB_norm_le (p : Sphere 2) : ‖productB p‖≤1 := by
  have hh := productSphere_norm_sq p
  have hn := Complex.normSq_eq_norm_sq (productB p)
  simp only [Complex.normSq_apply,productB_re,productB_im] at hn
  nlinarith [sq_nonneg ((p:Euclidean 3) 1),norm_nonneg (productB p)]
def productWeight (r : ℝ) (k : ℕ) (p : ThreeManifold) : ℝ :=
  ‖productA p.1‖^k+r^k*‖productB p.1‖^k
lemma productWeight_pos {r : ℝ} (hr : 0<r) (k : ℕ) (p : ThreeManifold) : 0<productWeight r k p := by
  rcases productAB_nonzero p.1 with ha | hb
  · exact add_pos_of_pos_of_nonneg (pow_pos (norm_pos_iff.mpr ha) _) (by positivity)
  · exact add_pos_of_nonneg_of_pos (by positivity) (mul_pos (pow_pos hr _) (pow_pos (norm_pos_iff.mpr hb) _))
lemma threeCoupled_direction_norm (r : ℝ) (k : ℕ) (p : ThreeManifold) (v : ThreeModel) (hv : ‖v‖≤1) :
    |fderiv ℝ (threeCoupled r k ∘ (chartAt ThreeModel p).symm) 0 v| ≤
      ‖fderiv ℝ (threeCoupled r k ∘ (chartAt ThreeModel p).symm) 0‖ := by
  have h := (fderiv ℝ (threeCoupled r k ∘ (chartAt ThreeModel p).symm) 0).le_opNorm v
  exact h.trans (mul_le_of_le_one_right (norm_nonneg _) hv)
lemma product_coefficient_bound {K L u x h : ℝ} (hK : 0<K) (_hL : 0≤L)
    (hx : |x|≤1) (hh : |K*(h-x*u)|≤L) : |h|≤L/K+|u| := by
  have ha : |h-x*u|≤L/K := by
    apply (le_div_iff₀ hK).mpr
    simpa only [abs_mul,abs_of_pos hK,mul_comm] using hh
  have hb : |x*u|≤|u| := by rw [abs_mul]; exact mul_le_of_le_one_left (abs_nonneg u) hx
  have hc := abs_add_le (h-x*u) (x*u)
  simp only [sub_add_cancel] at hc
  linarith
lemma threeCoupled_sprite_bounds (r : ℝ) (k : ℕ) (hk : 1≤k) (p : ThreeManifold) :
    let C := (p.2:ℂ)^k*productA p.1^(k-1)
    let D := (p.2:ℂ)^k*(r:ℂ)^k*productB p.1^(k-1)
    let L := ‖fderiv ℝ (threeCoupled r k ∘ (chartAt ThreeModel p).symm) 0‖
    |(C+D).re| ≤ L/(k:ℝ)+|threeCoupled r k p| ∧
    |C.im| ≤ L/(k:ℝ)+|threeCoupled r k p| ∧
    |D.im| ≤ L/(k:ℝ)+|threeCoupled r k p| := by
  dsimp only
  have hk' : (0:ℝ)<k := by exact_mod_cast (show 0<k by omega)
  have hh (i : Fin 3) := threeCoupled_direction_norm r k p (threeSphereDirection p i) (threeSphereDirection_norm p i)
  simp_rw [threeCoupled_sphere_direction r k hk p] at hh
  have h0 := product_coefficient_bound hk' (norm_nonneg _) (productAxis_coord_le p.1 0) (hh 0)
  have h1 := product_coefficient_bound hk' (norm_nonneg _) (productAxis_coord_le p.1 1) (hh 1)
  have h2 := product_coefficient_bound hk' (norm_nonneg _) (productAxis_coord_le p.1 2) (hh 2)
  norm_num [productA_axis,productB_axis,Fin.ext_iff] at h0 h1 h2
  refine ⟨h0, ?_, ?_⟩
  · simpa only [Complex.mul_re,Complex.mul_im,←neg_add,abs_neg,add_comm] using h1
  · simpa only [Complex.mul_re,Complex.mul_im,←neg_add,abs_neg,add_comm] using h2
lemma threeCoupled_value_bound (r : ℝ) (k : ℕ) (hk : 1≤k) (p : ThreeManifold) :
    ‖(productA p.1)^k+(r:ℂ)^k*(productB p.1)^k‖ ≤ |threeCoupled r k p|+
      ‖fderiv ℝ (threeCoupled r k ∘ (chartAt ThreeModel p).symm) 0‖/(k:ℝ) := by
  have hk' : (0:ℝ)<k := by exact_mod_cast (show 0<k by omega)
  have hi := threeCoupled_direction_norm r k p (threeCircleDirection p) (threeCircleDirection_norm p)
  rw [threeCoupled_circle_direction r k hk p,abs_mul,abs_neg,abs_of_pos hk'] at hi
  have him : |(threeCoupledComplex r k p).im|≤‖fderiv ℝ (threeCoupled r k ∘ (chartAt ThreeModel p).symm) 0‖/(k:ℝ) := by
    apply (le_div_iff₀ hk').mpr
    simpa only [mul_comm] using hi
  have hc := Complex.norm_le_abs_re_add_abs_im (threeCoupledComplex r k p)
  have hn : ‖threeCoupledComplex r k p‖=‖(productA p.1)^k+(r:ℂ)^k*(productB p.1)^k‖ := by
    simp only [threeCoupledComplex,norm_mul,norm_pow,p.2.norm_coe,one_pow,mul_one]
  rw [hn] at hc
  exact hc.trans (add_le_add (le_refl _) him)

theorem threeCoupled_global_noncancellation {r : ℝ} (hr : 0<r) (hr8 : r≤1/8)
    (k : ℕ) (hk : 2≤k) (p : ThreeManifold) :
    productWeight r k p ≤ 12*(|threeCoupled r k p|+
      ‖fderiv ℝ (threeCoupled r k ∘ (chartAt ThreeModel p).symm) 0‖/(k:ℝ)) := by
  have hw : ‖(p.2:ℂ)^k‖=1 := by simp only [norm_pow,p.2.norm_coe,one_pow]
  have hh := coupled_power_uniform_bound hr hr8 (productA_norm_le p.1) (productB_norm_le p.1) hw hk
  have hcoeff := threeCoupled_sprite_bounds r k (by omega : 1≤k) p
  have hval := threeCoupled_value_bound r k (by omega : 1≤k) p
  dsimp only at hcoeff
  unfold productWeight
  linarith [hcoeff.1,hcoeff.2.1,hcoeff.2.2]

end YauCounterexamples
end

end OAI
