import Mathlib
import OAI.Geometry.PrescribedPotential.CalabiCutoffAlgebra

namespace OAI

/-! Bernstein Quartic Algebra. -/

section

 
namespace BernsteinEstimate

lemma quadratic_root_bound {u C : ℝ} (hu : 0 ≤ u) (hC : 1 ≤ C)
    (h : u^2/2 ≤ C*u+2*C) : u^2 ≤ (2*C+2)^2 := by
  have hle : u ≤ 2*C+2 := by
    by_contra hn
    have hh : 2*C+2 < u := lt_of_not_ge hn
    nlinarith [mul_pos (by linarith : 0 < u-(2*C+2)) (by linarith : 0 < u+2)]
  exact pow_le_pow_left₀ hu hle 2

lemma weighted_quartic_bound {η T C : ℝ} (hη : 0 ≤ η) (hη1 : η ≤ 1)
    (hT : 0 ≤ T) (hC : 1 ≤ C)
    (h : η*T^2/2 ≤ C*η*T*Real.sqrt T+C*T+C) :
    η*T ≤ (2*C+2)^2 := by
  by_cases ht : T ≤ 1
  · have he := mul_le_mul hη1 ht hT (by norm_num : (0:ℝ) ≤ 1)
    nlinarith
  have ht' : 0 < T := by linarith
  have h1 : η*T/2 ≤ C*η*Real.sqrt T+2*C := by
    have hc : C ≤ C*T := le_mul_of_one_le_right (by linarith) (le_of_not_ge ht)
    have hh : T*(η*T/2) ≤ T*(C*η*Real.sqrt T+2*C) := by nlinarith only [h,hc]
    exact (mul_le_mul_iff_right₀ ht').mp hh
  let u := Real.sqrt (η*T)
  have hu : 0 ≤ u := Real.sqrt_nonneg _
  have hu2 : u^2 = η*T := Real.sq_sqrt (mul_nonneg hη hT)
  have hs : η*Real.sqrt T ≤ u := by
    apply (sq_le_sq₀ (mul_nonneg hη (Real.sqrt_nonneg _)) hu).mp
    rw [mul_pow,Real.sq_sqrt hT,hu2]
    exact mul_le_mul_of_nonneg_right (by nlinarith only [hη,hη1] : η^2 ≤ η) hT
  have h2 : u^2/2 ≤ C*u+2*C := by
    have hmul := mul_le_mul_of_nonneg_left hs (by linarith : 0 ≤ C)
    nlinarith only [h1,hmul,hu2]
  rw [← hu2]
  exact quadratic_root_bound hu hC h2

 

lemma quartic_max_reduction {η T r a B C LS LT Lη xs ys z : ℝ}
    (hη : 0 < η) (hη1 : η ≤ 1) (hT : 0 ≤ T) (hr : 0 ≤ r) (_hr2 : r^2=T)
    (hC : 1 ≤ C) (ha : 8*C+1 ≤ a) (haB : a ≤ B)
    (hLS : T-C ≤ LS) (hLT : -C*(1+T*r) ≤ LT) (hLη : -C ≤ Lη)
    (_hxs : 0 ≤ xs) (hys : 0 ≤ ys) (hxsB : xs ≤ C*η) (hysB : ys ≤ C*T)
    (hz : z^2 ≤ xs*ys)
    (hmax : η*a*LT+η*T*LS+a*T*Lη-2*η*T/a*ys-2*a*T/η*xs-2*T*z ≤ 0) :
    η*T^2/2 ≤ (B*C+C+3*B*C+4*C^2+1)*η*T*r +
      (B*C+C+3*B*C+4*C^2+1)*T + (B*C+C+3*B*C+4*C^2+1) := by
  have hC0 : 0 ≤ C := by linarith
  have ha0 : 0 < a := by linarith
  have hB0 : 0 ≤ B := by linarith
  have hyterm : 2*η*T/a*ys ≤ η*T^2/4 := by
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ ha0).mpr
    have hh := mul_le_mul_of_nonneg_left hysB (by positivity : 0 ≤ 2*η*T)
    have haa : 8*C ≤ a := by linarith
    have hhh := mul_le_mul_of_nonneg_right haa (by positivity : 0 ≤ η*T^2)
    nlinarith only [hh,hhh]
  have hxterm : 2*a*T/η*xs ≤ 2*B*C*T := by
    calc
      _ ≤ 2*a*T/η*(C*η) := mul_le_mul_of_nonneg_left hxsB (by positivity)
      _ = 2*a*C*T := by field_simp
      _ ≤ 2*B*C*T := by nlinarith only [mul_le_mul_of_nonneg_right haB (mul_nonneg hC0 hT)]
  have hzz : (-2*T*z)^2 ≤ 8*(C^2*T)*(η*T^2/2) := by
    have hh := hz.trans (mul_le_mul hxsB hysB hys (mul_nonneg hC0 hη.le))
    have hh' := mul_le_mul_of_nonneg_left hh (by positivity : 0 ≤ 4*T^2)
    nlinarith only [hh']
  have hcross := CalabiEstimate.cross_absorb (by positivity : 0 ≤ C^2*T)
    (by positivity : 0 ≤ η*T^2/2) hzz
  have h1 := mul_le_mul_of_nonneg_left hLT (by positivity : 0 ≤ η*a)
  have h2 := mul_le_mul_of_nonneg_left hLS (by positivity : 0 ≤ η*T)
  have h3 := mul_le_mul_of_nonneg_left hLη (by positivity : 0 ≤ a*T)
  have hab0 := mul_le_mul_of_nonneg_right haB (by positivity : 0 ≤ η*C)
  have hab1 := mul_le_mul_of_nonneg_right haB (by positivity : 0 ≤ η*C*T*r)
  have hab2 := mul_le_mul_of_nonneg_right haB (by positivity : 0 ≤ C*T)
  have heet := mul_le_mul_of_nonneg_right hη1 (by positivity : 0 ≤ C*T)
  have heec := mul_le_mul_of_nonneg_right hη1 (by positivity : 0 ≤ B*C)
  have herr0 : 0 ≤ (C+3*B*C+4*C^2+1)*η*T*r := by positivity
  have herr1 : 0 ≤ (B*C+1)*T := by positivity
  have herr2 : 0 ≤ C+3*B*C+4*C^2+1 := by positivity
  nlinarith only [hmax,h1,h2,h3,hyterm,hxterm,hcross,hab0,hab1,hab2,heet,heec,herr0,herr1,herr2]
end BernsteinEstimate

end

end OAI
