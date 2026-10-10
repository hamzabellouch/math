import OAI.Analysis.PlanarPacking.Nodes
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.SmoothTransition

namespace OAI

/-!
# Gaussian cardinal interpolation

The folded spectral representation gives the cardinal values and derivatives.
Gaussian damping then extends the radial cardinal functions to Schwartz functions.
-/

open scoped BigOperators ComplexConjugate ENNReal
open MeasureTheory



open MeasureTheory
open scoped ComplexConjugate

namespace SharpPlanar

lemma weighted_exp_integral (c : ℂ) (hc : c ≠ 0) (T : ℝ) :
    (∫ t in (0 : ℝ)..T, ((T : ℂ)-t)*Complex.exp (c*t)) =
      (Complex.exp (c*T)-1-c*T)/c^2 := by
  let F : ℝ → ℂ := fun t => (((T : ℂ)-t)*Complex.exp (c*t))/c +
      Complex.exp (c*t)/c^2
  have hd (t : ℝ) : HasDerivAt F (((T : ℂ)-t)*Complex.exp (c*t)) t := by
    have he : HasDerivAt (fun t : ℝ => Complex.exp (c*t))
        (Complex.exp (c*t)*c) t := by
      convert (((hasDerivAt_id (t : ℂ)).const_mul c).comp_ofReal).cexp using 1 <;> simp
    have ht : HasDerivAt (fun t : ℝ => (T : ℂ)-t) (-1) t := by
      convert ((hasDerivAt_id (t : ℂ)).const_sub (T : ℂ)).comp_ofReal using 1; simp
    convert ((ht.mul he).div_const c).add (he.div_const (c^2)) using 1
    all_goals first | rfl | (field_simp [hc]; ring)
  have hi : IntervalIntegrable (fun t : ℝ => ((T : ℂ)-t)*Complex.exp (c*t)) volume 0 T :=
    (by fun_prop : Continuous _).intervalIntegrable _ _
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd t) hi]
  simp only [F, Complex.ofReal_zero, sub_self, zero_mul, mul_zero, Complex.exp_zero,
    sub_zero, zero_div]
  field_simp
  ring

lemma exponential_division_one (U T : ℝ) (hu : U ≠ 0) :
    (Complex.exp (Complex.I*Real.pi*T*U)-1)/(U : ℂ) =
      Complex.I*Real.pi * ∫ t in (0 : ℝ)..T,
        Complex.exp (Complex.I*Real.pi*t*U) := by
  have hc : Complex.I*(Real.pi : ℂ)*(U : ℂ) ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero Complex.I_ne_zero (by exact_mod_cast Real.pi_ne_zero))
      (by exact_mod_cast hu)
  have he : (fun t : ℝ => Complex.exp (Complex.I*Real.pi*t*U)) =
      (fun t : ℝ => Complex.exp ((Complex.I*Real.pi*(U : ℂ))*t)) := by
    funext t; congr 1; ring
  rw [he, integral_exp_mul_complex hc]
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero]
  field_simp

lemma exponential_division_two (U T : ℝ) (hu : U ≠ 0) :
    (Complex.exp (Complex.I*Real.pi*T*U)-1-Complex.I*Real.pi*T*U)/(U : ℂ)^2 =
      -(Real.pi : ℂ)^2 * ∫ t in (0 : ℝ)..T,
        ((T : ℂ)-t)*Complex.exp (Complex.I*Real.pi*t*U) := by
  have hc : Complex.I*(Real.pi : ℂ)*(U : ℂ) ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero Complex.I_ne_zero (by exact_mod_cast Real.pi_ne_zero))
      (by exact_mod_cast hu)
  have he : (fun t : ℝ => ((T : ℂ)-t)*Complex.exp (Complex.I*Real.pi*t*U)) =
      (fun t : ℝ => ((T : ℂ)-t)*Complex.exp ((Complex.I*Real.pi*(U : ℂ))*t)) := by
    funext t; congr 2; ring
  rw [he, weighted_exp_integral _ hc]
  have hh : Complex.I*Real.pi*(U : ℂ)*T = Complex.I*Real.pi*T*U := by ring
  rw [hh]
  field_simp
  simp [Complex.I_sq]
  ring

end SharpPlanar

namespace SharpPlanar

lemma triangular_piece_integrals (N : ℕ) (a : ℕ → ℝ) (f : ℕ → ℝ → ℂ)
    (hf : ∀ l, Continuous (f l)) :
    (∑ j ∈ Finset.range N, ∫ t in a j..a (j+1),
      ∑ l ∈ Finset.Icc (j+1) N, f l t) =
      ∑ l ∈ Finset.Icc 1 N, ∫ t in a 0..a l, f l t := by
  have ht (j : ℕ) : (∫ t in a j..a (j+1),
      ∑ l ∈ Finset.Icc (j+1) N, f l t) =
      ∑ l ∈ Finset.Icc (j+1) N, ∫ t in a j..a (j+1), f l t := by
    exact intervalIntegral.integral_finsetSum fun l _ => (hf l).intervalIntegrable _ _
  simp_rw [ht]
  have hswap := Finset.sum_Ico_Ico_comm' 0 (N+1)
    (fun j l => ∫ t in a j..a (j+1), f l t)
  have hi (j : ℕ) : Finset.Ico (j+1) (N+1) = Finset.Icc (j+1) N := by
    ext l
    simp only [Finset.mem_Ico, Finset.mem_Icc]
    omega
  simp only [Nat.Ico_zero_eq_range, hi] at hswap
  have hleft : (∑ j ∈ Finset.range (N+1),
      ∑ l ∈ Finset.Icc (j+1) N, ∫ t in a j..a (j+1), f l t) =
      ∑ j ∈ Finset.range N,
        ∑ l ∈ Finset.Icc (j+1) N, ∫ t in a j..a (j+1), f l t := by
    rw [Finset.sum_range_succ]
    simp
  rw [hleft] at hswap
  rw [hswap]
  have hadj (l : ℕ) : (∑ j ∈ Finset.range l, ∫ t in a j..a (j+1), f l t) =
      ∫ t in a 0..a l, f l t := by
    exact intervalIntegral.sum_integral_adjacent_intervals
      (fun j _ => (hf l).intervalIntegrable _ _)
  simp_rw [hadj]
  symm
  apply Finset.sum_subset
  · intro l hl
    simp only [Finset.mem_Icc, Finset.mem_range] at *
    omega
  · intro l hl hn
    have : l = 0 := by
      simp only [Finset.mem_Icc, Finset.mem_range, not_and, not_le] at *
      omega
    simp [this]

noncomputable def foldedU (n : ℕ) (s : ℝ) : ℝ :=
  (∑ j ∈ Finset.range 6, ∫ t in (j : ℝ)/6..((j : ℝ)+1)/6,
    u n j t * Complex.exp (Complex.I*Real.pi*(t:ℂ)*s)).re

noncomputable def foldedV (n : ℕ) (s : ℝ) : ℝ :=
  (∑ j ∈ Finset.range 6, ∫ t in (j : ℝ)/6..((j : ℝ)+1)/6,
    v n j t * Complex.exp (Complex.I*Real.pi*(t:ℂ)*s)).re

lemma u_integrand (n j : ℕ) (s t : ℝ) :
    u n j t * Complex.exp (Complex.I*Real.pi*(t:ℂ)*s) =
    ∑ l ∈ Finset.Icc (j+1) 6,
      2*Pcoeff l*Complex.exp (Complex.I*Real.pi*((l:ℝ)/6:ℝ)*n)*
        (-(Real.pi:ℂ)^2*((l:ℂ)/6-t)*
          Complex.exp (Complex.I*Real.pi*(t:ℂ)*(s-n))) := by
  unfold u
  simp_rw [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro l hl
  have he : Complex.exp (-Complex.I*Real.pi*(t:ℂ)*n) *
      Complex.exp (Complex.I*Real.pi*(t:ℂ)*s) =
      Complex.exp (Complex.I*Real.pi*(t:ℂ)*(s-n)) := by
    rw [← Complex.exp_add]
    congr 1
    ring
  push_cast
  rw [show Complex.I*Real.pi*(l:ℂ)/6*n = Complex.I*Real.pi*((l:ℂ)/6)*n by ring]
  calc
    _ = 2*Pcoeff l*Complex.exp (Complex.I*Real.pi*((l:ℂ)/6)*n)*
      (-(Real.pi:ℂ)^2*((l:ℂ)/6-t)*
        (Complex.exp (-Complex.I*Real.pi*(t:ℂ)*n)*
          Complex.exp (Complex.I*Real.pi*(t:ℂ)*s))) := by ring
    _ = _ := by rw [he]

lemma v_integrand (n j : ℕ) (s t : ℝ) :
    v n j t * Complex.exp (Complex.I*Real.pi*(t:ℂ)*s) =
    ∑ l ∈ Finset.Icc (j+1) 6,
      2*Pcoeff l*Complex.exp (Complex.I*Real.pi*((l:ℝ)/6:ℝ)*n)*
        (Complex.I*Real.pi*Complex.exp (Complex.I*Real.pi*(t:ℂ)*(s-n))) := by
  unfold v
  simp_rw [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro l hl
  have he : Complex.exp (-Complex.I*Real.pi*(t:ℂ)*n) *
      Complex.exp (Complex.I*Real.pi*(t:ℂ)*s) =
      Complex.exp (Complex.I*Real.pi*(t:ℂ)*(s-n)) := by
    rw [← Complex.exp_add]
    congr 1
    ring
  push_cast
  rw [show Complex.I*Real.pi*(l:ℂ)/6*n = Complex.I*Real.pi*((l:ℂ)/6)*n by ring]
  calc
    _ = 2*Pcoeff l*Complex.exp (Complex.I*Real.pi*((l:ℂ)/6)*n)*
      (Complex.I*Real.pi*
        (Complex.exp (-Complex.I*Real.pi*(t:ℂ)*n)*
          Complex.exp (Complex.I*Real.pi*(t:ℂ)*s))) := by ring
    _ = _ := by rw [he]

end SharpPlanar

namespace SharpPlanar

lemma P_as_table (s : ℝ) : P s =
    ∏ a ∈ residues,
      (2 - 2*(Real.cos (Real.pi*s/6)*cosTable a + Real.sin (Real.pi*s/6)*sinTable a)) := by
  unfold P
  apply Finset.prod_congr rfl
  intro a ha
  rw [squared_sine_to_cos,
    show 2*(Real.pi*(s-a)/12) = Real.pi*s/6-Real.pi*a/6 by ring, Real.cos_sub]
  rw [(trig_table a (by have := residue_lt ha; omega)).1,
    (trig_table a (by have := residue_lt ha; omega)).2]

lemma polynomial_reduce (c d : ℝ) (hcd : c^2+d^2=1) :
    (2-2*c)*(2-2*(c*b+d/2))*(2-2*d)*(2+c-2*b*d)*(2+2*(c*b+d/2))*(2+2*d) =
      (4*(c/2+b*d)^2-3)^2*(1-2*(c/2+b*d))^2 := by
  have hd2 : d^2 = 1-c^2 := by linarith
  have hd3 : d^3 = (1-c^2)*d := by rw [pow_succ, hd2]
  have hd4 : d^4 = (1-c^2)^2 := by rw [show (4 : ℕ) = 2*2 by norm_num, pow_mul, hd2]
  have hd5 : d^5 = (1-c^2)^2*d := by rw [pow_succ, hd4]
  have hd6 : d^6 = (1-c^2)^3 := by rw [show (6 : ℕ) = 2*3 by norm_num, pow_mul, hd2]
  ring_nf
  simp only [b_sq, b_pow_3, b_pow_4, b_pow_5, b_pow_6, hd2, hd3, hd4, hd5, hd6]
  ring

lemma P_cos_factor (s : ℝ) : P s =
    (4*Real.cos (Real.pi*(s-2)/6)^2-3)^2 *
      (1-2*Real.cos (Real.pi*(s-2)/6))^2 := by
  rw [P_as_table]
  norm_num [residues, cosTable, sinTable]
  rw [show Real.pi*(s-2)/6=Real.pi*s/6-Real.pi/3 by ring,
    Real.cos_sub, Real.cos_pi_div_three, Real.sin_pi_div_three]
  change _ = (4*(Real.cos (Real.pi*s/6)*(1/2)+Real.sin (Real.pi*s/6)*b)^2-3)^2 *
    (1-2*(Real.cos (Real.pi*s/6)*(1/2)+Real.sin (Real.pi*s/6)*b))^2
  convert polynomial_reduce (Real.cos (Real.pi*s/6)) (Real.sin (Real.pi*s/6))
    (by nlinarith [Real.sin_sq_add_cos_sq (Real.pi*s/6)]) using 1 <;> ring

end SharpPlanar

namespace SharpPlanar

lemma phase_nat (j : ℕ) (s : ℝ) :
    Complex.exp (Complex.I * Real.pi * ((j : ℝ)/6 : ℝ) * s) =
      ((Real.cos (Real.pi*s/6) : ℂ) + Real.sin (Real.pi*s/6)*Complex.I)^j := by
  rw [show Complex.I * Real.pi * ((j : ℝ)/6 : ℝ) * s =
      (j : ℂ) * ((Real.pi*s/6 : ℝ) * Complex.I) by push_cast; ring,
    Complex.exp_nat_mul, Complex.exp_ofReal_mul_I]

lemma polynomial_fourier_algebra (c d : ℝ) (hcd : c^2+d^2=1) :
    (∏ a ∈ residues, (2-2*(c*cosTable a+d*sinTable a))) =
    (Pcoeff 0 + ∑ j ∈ Finset.Icc (1 : ℕ) 6,
      2*Pcoeff j*((c : ℂ)+(d : ℂ)*Complex.I)^j).re := by
  have hd2 : d^2 = 1-c^2 := by linarith
  have hd3 : d^3 = (1-c^2)*d := by rw [pow_succ, hd2]
  have hd4 : d^4 = (1-c^2)^2 := by rw [show (4 : ℕ) = 2*2 by norm_num, pow_mul, hd2]
  have hd5 : d^5 = (1-c^2)^2*d := by rw [pow_succ, hd4]
  have hd6 : d^6 = (1-c^2)^3 := by rw [show (6 : ℕ) = 2*3 by norm_num, pow_mul, hd2]
  norm_num [residues, cosTable, sinTable, Finset.sum_Icc_succ_top, Pcoeff,
    pow_succ, Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im]
  ring_nf
  simp only [b_sq, b_pow_3, hd2, hd3, hd4, hd5, hd6]
  ring


theorem P_fourier (s : ℝ) :
    P s = (Pcoeff 0 + ∑ j ∈ Finset.Icc (1 : ℕ) 6,
      2*Pcoeff j*Complex.exp (Complex.I*Real.pi*((j : ℝ)/6 : ℝ)*s)).re := by
  simp_rw [phase_nat]
  rw [P_as_table]
  exact polynomial_fourier_algebra _ _ (by nlinarith [Real.sin_sq_add_cos_sq (Real.pi*s/6)])

end SharpPlanar

namespace SharpPlanar

noncomputable def Pmoment (ell : ℕ) (s : ℝ) : ℝ :=
  (Pcoeff 0 * (0 : ℂ)^ell + ∑ j ∈ Finset.Icc (1 : ℕ) 6,
    2*Pcoeff j*(Complex.I*Real.pi*((j : ℝ)/6 : ℝ))^ell *
      Complex.exp (Complex.I*Real.pi*((j : ℝ)/6 : ℝ)*s)).re

lemma Pmoment_zero (s : ℝ) : Pmoment 0 s = P s := by
  rw [P_fourier]
  simp [Pmoment]

lemma Pmoment_hasDerivAt (ell : ℕ) (s : ℝ) :
    HasDerivAt (Pmoment ell) (Pmoment (ell+1) s) s := by
  have hh (j : ℕ) : HasDerivAt (fun s : ℝ =>
      2*Pcoeff j*(Complex.I*Real.pi*((j : ℝ)/6 : ℝ))^ell *
        Complex.exp (Complex.I*Real.pi*((j : ℝ)/6 : ℝ)*s))
      (2*Pcoeff j*(Complex.I*Real.pi*((j : ℝ)/6 : ℝ))^(ell+1) *
        Complex.exp (Complex.I*Real.pi*((j : ℝ)/6 : ℝ)*s)) s := by
    have he := (((hasDerivAt_id (s : ℂ)).const_mul
      (Complex.I*Real.pi*((j : ℝ)/6 : ℝ))).comp_ofReal).cexp.const_mul
        (2*Pcoeff j*(Complex.I*Real.pi*((j : ℝ)/6 : ℝ))^ell)
    convert he using 1 <;> first | rfl | (simp only [mul_one, pow_succ, id_eq]; ring)
  have hd := ((hasDerivAt_const s (Pcoeff 0*(0 : ℂ)^ell)).add
    (HasDerivAt.fun_sum (fun j (_ : j ∈ Finset.Icc (1 : ℕ) 6) => hh j)))
  have hdr := Complex.reCLM.hasFDerivAt.comp_hasDerivAt s hd
  convert hdr using 1 <;> first | rfl | simp [Pmoment]

lemma trig_nat_mod12 (n : ℕ) :
    Real.sin (Real.pi*n/6) = sinTable (n%12) ∧
    Real.cos (Real.pi*n/6) = cosTable (n%12) := by
  have hn : (n : ℝ) = (n%12 : ℕ) + 12*(n/12 : ℕ) := by
    exact_mod_cast (Nat.mod_add_div n 12).symm
  have ha : Real.pi*n/6 = Real.pi*(n%12 : ℕ)/6 + (n/12 : ℕ)*(2*Real.pi) := by
    conv_lhs => rw [hn]
    ring
  rw [ha, Real.sin_add_nat_mul_two_pi, Real.cos_add_nat_mul_two_pi]
  exact trig_table (n%12) (by omega)

lemma Pmoment_mod (ell n : ℕ) : Pmoment ell n = Pmoment ell (n%12 : ℕ) := by
  unfold Pmoment
  simp only [phase_nat]
  rw [(trig_nat_mod12 n).1, (trig_nat_mod12 n).2,
    (trig_table (n%12) (by omega)).1, (trig_table (n%12) (by omega)).2]


lemma phase_node (j n : ℕ) :
    Complex.exp (Complex.I*Real.pi*((j : ℝ)/6 : ℝ)*(n : ℝ)) =
      (cosTable ((j*n)%12) : ℂ) + sinTable ((j*n)%12)*Complex.I := by
  rw [show Complex.I*Real.pi*((j : ℝ)/6 : ℝ)*(n : ℝ) =
      ((Real.pi*(j*n : ℕ)/6 : ℝ):ℂ)*Complex.I by push_cast; ring,
    Complex.exp_ofReal_mul_I, (trig_nat_mod12 (j*n)).1, (trig_nat_mod12 (j*n)).2]

lemma Pmoment_node_formula (ell n : ℕ) :
    Pmoment ell n =
      (Pcoeff 0*(0 : ℂ)^ell + ∑ j ∈ Finset.Icc (1 : ℕ) 6,
        2*Pcoeff j*(Complex.I*Real.pi*((j : ℝ)/6 : ℝ))^ell *
          ((cosTable ((j*n)%12) : ℂ) + sinTable ((j*n)%12)*Complex.I)).re := by
  unfold Pmoment
  simp_rw [phase_node]

lemma Pmoment_node_0 :
    Pmoment 0 (0 : ℕ) = 0 ∧ Pmoment 1 (0 : ℕ) = 0 ∧
      Pmoment 2 (0 : ℕ) = 2*Q 0 ∧ Pmoment 3 (0 : ℕ) = 6*Q 0*D 0 := by
  rw [Q_0, D_0, Pmoment_node_formula 0 0, Pmoment_node_formula 1 0,
    Pmoment_node_formula 2 0, Pmoment_node_formula 3 0]
  norm_num [Finset.sum_Icc_succ_top, cosTable, sinTable, Pcoeff,
    pow_succ, Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im]
  all_goals repeat' constructor
  all_goals try ring_nf

lemma Pmoment_node_1 :
    Pmoment 0 (1 : ℕ) = 0 ∧ Pmoment 1 (1 : ℕ) = 0 ∧
      Pmoment 2 (1 : ℕ) = 2*Q 1 ∧ Pmoment 3 (1 : ℕ) = 6*Q 1*D 1 := by
  rw [Q_1, D_1, Pmoment_node_formula 0 1, Pmoment_node_formula 1 1,
    Pmoment_node_formula 2 1, Pmoment_node_formula 3 1]
  norm_num [Finset.sum_Icc_succ_top, cosTable, sinTable, Pcoeff,
    pow_succ, Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im]
  all_goals repeat' constructor
  all_goals try ring_nf
  all_goals simp only [b_sq]
  all_goals first | trivial | ring

lemma Pmoment_node_3 :
    Pmoment 0 (3 : ℕ) = 0 ∧ Pmoment 1 (3 : ℕ) = 0 ∧
      Pmoment 2 (3 : ℕ) = 2*Q 3 ∧ Pmoment 3 (3 : ℕ) = 6*Q 3*D 3 := by
  rw [Q_3, D_3, Pmoment_node_formula 0 3, Pmoment_node_formula 1 3,
    Pmoment_node_formula 2 3, Pmoment_node_formula 3 3]
  norm_num [Finset.sum_Icc_succ_top, cosTable, sinTable, Pcoeff,
    pow_succ, Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im]
  all_goals repeat' constructor
  all_goals try ring_nf
  all_goals simp only [b_sq]
  all_goals first | trivial | ring

lemma Pmoment_node_4 :
    Pmoment 0 (4 : ℕ) = 0 ∧ Pmoment 1 (4 : ℕ) = 0 ∧
      Pmoment 2 (4 : ℕ) = 2*Q 4 ∧ Pmoment 3 (4 : ℕ) = 6*Q 4*D 4 := by
  rw [Q_4, D_4, Pmoment_node_formula 0 4, Pmoment_node_formula 1 4,
    Pmoment_node_formula 2 4, Pmoment_node_formula 3 4]
  norm_num [Finset.sum_Icc_succ_top, cosTable, sinTable, Pcoeff,
    pow_succ, Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im]
  all_goals repeat' constructor
  all_goals try ring_nf
  all_goals simp only [b_sq]
  all_goals first | trivial | ring

lemma Pmoment_node_7 :
    Pmoment 0 (7 : ℕ) = 0 ∧ Pmoment 1 (7 : ℕ) = 0 ∧
      Pmoment 2 (7 : ℕ) = 2*Q 7 ∧ Pmoment 3 (7 : ℕ) = 6*Q 7*D 7 := by
  rw [Q_7, D_7, Pmoment_node_formula 0 7, Pmoment_node_formula 1 7,
    Pmoment_node_formula 2 7, Pmoment_node_formula 3 7]
  norm_num [Finset.sum_Icc_succ_top, cosTable, sinTable, Pcoeff,
    pow_succ, Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im]
  all_goals repeat' constructor
  all_goals try ring_nf
  all_goals simp only [b_sq]
  all_goals first | trivial | ring

lemma Pmoment_node_9 :
    Pmoment 0 (9 : ℕ) = 0 ∧ Pmoment 1 (9 : ℕ) = 0 ∧
      Pmoment 2 (9 : ℕ) = 2*Q 9 ∧ Pmoment 3 (9 : ℕ) = 6*Q 9*D 9 := by
  rw [Q_9, D_9, Pmoment_node_formula 0 9, Pmoment_node_formula 1 9,
    Pmoment_node_formula 2 9, Pmoment_node_formula 3 9]
  norm_num [Finset.sum_Icc_succ_top, cosTable, sinTable, Pcoeff,
    pow_succ, Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im]
  all_goals repeat' constructor
  all_goals try ring_nf
  all_goals simp only [b_sq]
  all_goals first | trivial | ring


theorem Pmoment_node_data (n : ℕ) (hn : n%12 ∈ residues) :
    Pmoment 0 n = 0 ∧ Pmoment 1 n = 0 ∧
      Pmoment 2 n = 2*Q n ∧ Pmoment 3 n = 6*Q n*D n := by
  rw [Pmoment_mod 0 n, Pmoment_mod 1 n, Pmoment_mod 2 n, Pmoment_mod 3 n,
    ← Q_mod n, ← D_mod n]
  simp only [residues, Finset.mem_insert, Finset.mem_singleton] at hn
  rcases hn with hn | hn | hn | hn | hn | hn <;> rw [hn]
  · exact Pmoment_node_0
  · exact Pmoment_node_1
  · exact Pmoment_node_3
  · exact Pmoment_node_4
  · exact Pmoment_node_7
  · exact Pmoment_node_9

end SharpPlanar

namespace SharpPlanar

lemma foldedU_unfold (n : ℕ) (s : ℝ) : foldedU n s =
    (∑ l ∈ Finset.Icc (1 : ℕ) 6, ∫ t in (0 : ℝ)..((l : ℝ)/6),
      2*Pcoeff l*Complex.exp (Complex.I*Real.pi*((l:ℝ)/6:ℝ)*n)*
        (-(Real.pi:ℂ)^2*((l:ℂ)/6-t)*
          Complex.exp (Complex.I*Real.pi*(t:ℂ)*(s-n)))).re := by
  unfold foldedU
  simp_rw [u_integrand]
  congr 1
  convert triangular_piece_integrals 6 (fun j => (j : ℝ)/6)
    (fun l t => 2*Pcoeff l*Complex.exp (Complex.I*Real.pi*((l:ℝ)/6:ℝ)*n)*
        (-(Real.pi:ℂ)^2*((l:ℂ)/6-t)*
          Complex.exp (Complex.I*Real.pi*(t:ℂ)*(s-n)))) (fun l => by fun_prop) using 1 <;>
    simp only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, zero_div]

lemma foldedV_unfold (n : ℕ) (s : ℝ) : foldedV n s =
    (∑ l ∈ Finset.Icc (1 : ℕ) 6, ∫ t in (0 : ℝ)..((l : ℝ)/6),
      2*Pcoeff l*Complex.exp (Complex.I*Real.pi*((l:ℝ)/6:ℝ)*n)*
        (Complex.I*Real.pi*Complex.exp (Complex.I*Real.pi*(t:ℂ)*(s-n)))).re := by
  unfold foldedV
  simp_rw [v_integrand]
  congr 1
  convert triangular_piece_integrals 6 (fun j => (j : ℝ)/6)
    (fun l t => 2*Pcoeff l*Complex.exp (Complex.I*Real.pi*((l:ℝ)/6:ℝ)*n)*
        (Complex.I*Real.pi*Complex.exp (Complex.I*Real.pi*(t:ℂ)*(s-n))))
      (fun l => by fun_prop) using 1 <;>
    simp only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, zero_div]

lemma foldedU_divided (n : ℕ) (s : ℝ) (hs : s ≠ n) : foldedU n s =
    (∑ l ∈ Finset.Icc (1 : ℕ) 6,
      2*Pcoeff l*Complex.exp (Complex.I*Real.pi*((l:ℝ)/6:ℝ)*n)*
        ((Complex.exp (Complex.I*Real.pi*((l:ℝ)/6:ℝ)*(s-n))-1-
          Complex.I*Real.pi*((l:ℝ)/6:ℝ)*(s-n))/(s-n : ℝ)^2)).re := by
  rw [foldedU_unfold]
  congr 1
  apply Finset.sum_congr rfl
  intro l hl
  rw [intervalIntegral.integral_const_mul]
  congr 1
  have he := exponential_division_two (s-n) (l/6) (sub_ne_zero.mpr hs)
  push_cast at he ⊢
  rw [he]
  rw [← intervalIntegral.integral_const_mul]
  congr 1
  funext t
  ring

lemma foldedV_divided (n : ℕ) (s : ℝ) (hs : s ≠ n) : foldedV n s =
    (∑ l ∈ Finset.Icc (1 : ℕ) 6,
      2*Pcoeff l*Complex.exp (Complex.I*Real.pi*((l:ℝ)/6:ℝ)*n)*
        ((Complex.exp (Complex.I*Real.pi*((l:ℝ)/6:ℝ)*(s-n))-1)/(s-n : ℝ))).re := by
  rw [foldedV_unfold]
  congr 1
  apply Finset.sum_congr rfl
  intro l hl
  rw [intervalIntegral.integral_const_mul]
  congr 1
  have he := exponential_division_one (s-n) (l/6) (sub_ne_zero.mpr hs)
  push_cast at he ⊢
  rw [he, intervalIntegral.integral_const_mul]


lemma exp_phase_split (T s v : ℝ) :
    Complex.exp (Complex.I*Real.pi*T*v)*
      Complex.exp (Complex.I*Real.pi*T*(s-v)) =
        Complex.exp (Complex.I*Real.pi*T*s) := by
  rw [← Complex.exp_add]
  congr 1
  ring

lemma foldedU_quotient (n : ℕ) (s : ℝ) (hs : s ≠ n) :
    foldedU n s = (P s-P n-Pmoment 1 n*(s-n))/(s-n)^2 := by
  rw [foldedU_divided n s hs]
  have ht (l : ℕ) :
      2*Pcoeff l*Complex.exp (Complex.I*Real.pi*((l:ℝ)/6:ℝ)*n)*
        ((Complex.exp (Complex.I*Real.pi*((l:ℝ)/6:ℝ)*(s-n))-1-
          Complex.I*Real.pi*((l:ℝ)/6:ℝ)*(s-n))/(s-n : ℝ)^2) =
      (2*Pcoeff l*Complex.exp (Complex.I*Real.pi*((l:ℝ)/6:ℝ)*s)-
        2*Pcoeff l*Complex.exp (Complex.I*Real.pi*((l:ℝ)/6:ℝ)*n)-
        (2*Pcoeff l*(Complex.I*Real.pi*((l:ℝ)/6:ℝ))*
          Complex.exp (Complex.I*Real.pi*((l:ℝ)/6:ℝ)*n))*(s-n : ℝ))/(s-n : ℝ)^2 := by
    rw [← mul_div_assoc]
    congr 1
    have he := exp_phase_split ((l:ℝ)/6) s n
    push_cast at he ⊢
    calc
      _ = 2*Pcoeff l*(Complex.exp (Complex.I*Real.pi*(l/6 : ℝ)*n)*
          Complex.exp (Complex.I*Real.pi*(l/6 : ℝ)*(s-n)))-
          2*Pcoeff l*Complex.exp (Complex.I*Real.pi*(l/6 : ℝ)*n)-
          (2*Pcoeff l*(Complex.I*Real.pi*(l/6 : ℝ))*
            Complex.exp (Complex.I*Real.pi*(l/6 : ℝ)*n))*(s-n : ℝ) := by push_cast; ring
      _ = _ := by push_cast; rw [he]
  simp_rw [ht]
  rw [← Finset.sum_div]
  rw [← Complex.ofReal_pow, Complex.div_ofReal_re]
  congr 1
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.sum_mul]
  rw [P_fourier s, P_fourier n]
  simp [Pmoment, Complex.mul_re]

lemma foldedV_quotient (n : ℕ) (s : ℝ) (hs : s ≠ n) :
    foldedV n s = (P s-P n)/(s-n) := by
  rw [foldedV_divided n s hs]
  have ht (l : ℕ) :
      2*Pcoeff l*Complex.exp (Complex.I*Real.pi*((l:ℝ)/6:ℝ)*n)*
        ((Complex.exp (Complex.I*Real.pi*((l:ℝ)/6:ℝ)*(s-n))-1)/(s-n : ℝ)) =
      (2*Pcoeff l*Complex.exp (Complex.I*Real.pi*((l:ℝ)/6:ℝ)*s)-
        2*Pcoeff l*Complex.exp (Complex.I*Real.pi*((l:ℝ)/6:ℝ)*n))/(s-n : ℝ) := by
    rw [← mul_div_assoc]
    congr 1
    have he := exp_phase_split ((l:ℝ)/6) s n
    push_cast at he ⊢
    calc
      _ = 2*Pcoeff l*(Complex.exp (Complex.I*Real.pi*(l/6 : ℝ)*n)*
          Complex.exp (Complex.I*Real.pi*(l/6 : ℝ)*(s-n)))-
          2*Pcoeff l*Complex.exp (Complex.I*Real.pi*(l/6 : ℝ)*n) := by push_cast; ring
      _ = _ := by push_cast; rw [he]
  simp_rw [ht]
  rw [← Finset.sum_div, Complex.div_ofReal_re]
  congr 1
  rw [Finset.sum_sub_distrib, P_fourier s, P_fourier n]
  simp [Complex.mul_re]

lemma folded_basis_quotients (n : ℕ) (hn : n%12 ∈ residues) (s : ℝ) (hs : s ≠ n) :
    foldedU n s = P s/(s-n)^2 ∧ foldedV n s = P s/(s-n) := by
  obtain ⟨h0,h1,-,-⟩ := Pmoment_node_data n hn
  rw [Pmoment_zero] at h0
  rw [foldedU_quotient n s hs, foldedV_quotient n s hs, h0, h1]
  simp

end SharpPlanar



open Set Filter MeasureTheory
open scoped Topology FourierTransform ContDiff

namespace SharpPlanar

lemma fourierIntegral_temperate {μ : Measure ℝ} (L : ℝ →L[ℝ] ℝ →L[ℝ] ℝ)
    {f : ℝ → ℂ} (hf : Integrable f μ)
    (hm : ∀ n : ℕ, Integrable (fun t => ‖t‖^n * ‖f t‖) μ) :
    Function.HasTemperateGrowth (VectorFourier.fourierIntegral 𝐞 μ L.toLinearMap₁₂ f) := by
  refine ⟨VectorFourier.contDiff_fourierIntegral L (fun n _ => hm n), fun n => ?_⟩
  refine ⟨0, ∫ t, ‖VectorFourier.fourierPowSMulRight L f t n‖ ∂μ, fun s => ?_⟩
  rw [VectorFourier.iteratedFDeriv_fourierIntegral L
    (N := (⊤ : ℕ∞)) (fun n _ => hm n) hf.aestronglyMeasurable (by simp)]
  simpa only [pow_zero, mul_one] using
    VectorFourier.norm_fourierIntegral_le_integral_norm 𝐞 μ L.toLinearMap₁₂
      (fun t => VectorFourier.fourierPowSMulRight L f t n) s

noncomputable def spectral (μ : Measure ℝ) (f : ℝ → ℂ) (s : ℝ) : ℂ :=
  ∫ t, Complex.exp (((Real.pi*t*s : ℝ) : ℂ)*Complex.I) * f t ∂μ

noncomputable def spectralForm : ℝ →L[ℝ] ℝ →L[ℝ] ℝ :=
  (-1/2 : ℝ) • ContinuousLinearMap.mul ℝ ℝ

lemma spectral_eq (μ : Measure ℝ) (f : ℝ → ℂ) : spectral μ f =
    VectorFourier.fourierIntegral 𝐞 μ spectralForm.toLinearMap₁₂ f := by
  funext s
  unfold spectral VectorFourier.fourierIntegral
  apply integral_congr_ae
  filter_upwards with t
  have hL : spectralForm.toLinearMap₁₂ t s = (-1/2 : ℝ)*t*s := by
    change (-1/2 : ℝ)*(t*s) = _
    ring
  rw [hL]
  simp only [Circle.smul_def, Real.fourierChar_apply, smul_eq_mul]
  congr 2
  push_cast
  ring

lemma spectral_temperate {μ : Measure ℝ} {f : ℝ → ℂ} (hf : Integrable f μ)
    (hm : ∀ n : ℕ, Integrable (fun t => ‖t‖^n * ‖f t‖) μ) :
    Function.HasTemperateGrowth (spectral μ f) := by
  rw [spectral_eq]
  exact fourierIntegral_temperate spectralForm hf hm

lemma integrable_moment_Icc {a b : ℝ} {f : ℝ → ℂ}
    (hf : IntegrableOn f (Icc a b)) (n : ℕ) :
    Integrable (fun t => ‖t‖^n * ‖f t‖) (volume.restrict (Icc a b)) := by
  have hc : ContinuousOn (fun t : ℝ => ‖t‖^n) (Icc a b) := by fun_prop
  exact IntegrableOn.continuousOn_mul hc hf.norm isCompact_Icc

lemma spectral_Icc_temperate {a b : ℝ} {f : ℝ → ℂ}
    (hf : IntegrableOn f (Icc a b)) :
    Function.HasTemperateGrowth (spectral (volume.restrict (Icc a b)) f) :=
  spectral_temperate hf (integrable_moment_Icc hf)

end SharpPlanar

namespace SharpPlanar

lemma spectral_integrable {μ : Measure ℝ} {f : ℝ → ℂ}
    (hf : Integrable f μ) (s : ℝ) :
    Integrable (fun t => Complex.exp (((Real.pi*t*s : ℝ):ℂ)*Complex.I)*f t) μ := by
  refine (hf.norm).mono' ?_ ?_
  · exact (by fun_prop : Continuous (fun t : ℝ =>
        Complex.exp (((Real.pi*t*s : ℝ):ℂ)*Complex.I))).aestronglyMeasurable.mul
      hf.aestronglyMeasurable
  · filter_upwards with t
    simp [Complex.norm_exp]

lemma spectral_hasDerivAt {μ : Measure ℝ} {f : ℝ → ℂ}
    (hf : Integrable f μ) (hm : Integrable (fun t => ‖t‖*‖f t‖) μ) (s : ℝ) :
    HasDerivAt (spectral μ f)
      (spectral μ (fun t => ((Real.pi*t : ℝ):ℂ)*Complex.I*f t) s) s := by
  have hf' : Integrable (fun t => ((Real.pi*t : ℝ):ℂ)*Complex.I*f t) μ := by
    refine (hm.const_mul Real.pi).mono' ?_ ?_
    · exact (((by fun_prop : Continuous (fun t : ℝ =>
          ((Real.pi*t : ℝ):ℂ)*Complex.I))).aestronglyMeasurable).mul hf.aestronglyMeasurable
    · filter_upwards with t
      simp [abs_of_pos Real.pi_pos, mul_assoc]
  have he (t x : ℝ) : HasDerivAt (fun x : ℝ =>
      Complex.exp (((Real.pi*t*x : ℝ):ℂ)*Complex.I)*f t)
      (Complex.exp (((Real.pi*t*x : ℝ):ℂ)*Complex.I)*
        (((Real.pi*t : ℝ):ℂ)*Complex.I*f t)) x := by
    convert ((((hasDerivAt_id x).const_mul (Real.pi*t)).ofReal_comp.mul_const
      Complex.I).cexp.mul_const (f t)) using 1 <;> first | rfl | (simp only [mul_one, id_eq]; ring)
  have hr := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := μ) (s := Set.univ) (bound := fun t => Real.pi*(‖t‖*‖f t‖))
    (F := fun x t => Complex.exp (((Real.pi*t*x : ℝ):ℂ)*Complex.I)*f t)
    (F' := fun x t => Complex.exp (((Real.pi*t*x : ℝ):ℂ)*Complex.I)*
      (((Real.pi*t : ℝ):ℂ)*Complex.I*f t))
    (Filter.univ_mem) (Filter.Eventually.of_forall fun x => (spectral_integrable hf x).aestronglyMeasurable)
    (spectral_integrable hf s) (spectral_integrable hf' s).aestronglyMeasurable
    (Filter.Eventually.of_forall fun t x _ => by
      simp [Complex.norm_exp, abs_of_pos Real.pi_pos, mul_assoc])
    (hm.const_mul Real.pi) (Filter.Eventually.of_forall fun t x _ => he t x)
  exact hr.2

end SharpPlanar

namespace SharpPlanar
open MeasureTheory Set

lemma interval_spectral_eq (f : ℝ → ℂ) {a b : ℝ} (hab : a ≤ b) (s : ℝ) :
    (∫ t in a..b, f t * Complex.exp (Complex.I*Real.pi*(t:ℂ)*s)) =
      spectral (volume.restrict (Icc a b)) f s := by
  unfold spectral
  rw [intervalIntegral.integral_of_le hab, integral_Icc_eq_integral_Ioc]
  apply integral_congr_ae
  filter_upwards with t
  simp only [mul_comm (f t)]
  congr 1
  congr 1
  push_cast
  ring

lemma interval_exponential_hasDerivAt {f : ℝ → ℂ} {a b : ℝ}
    (hab : a ≤ b) (hf : ContinuousOn f (Icc a b)) (s : ℝ) :
    HasDerivAt (fun s : ℝ => ∫ t in a..b,
      f t * Complex.exp (Complex.I*Real.pi*(t:ℂ)*s))
      (∫ t in a..b, f t * (Complex.I*Real.pi*(t:ℂ)) *
        Complex.exp (Complex.I*Real.pi*(t:ℂ)*s)) s := by
  have hfi : IntegrableOn f (Icc a b) volume := hf.integrableOn_Icc
  have hder := spectral_hasDerivAt hfi (by
    simpa only [pow_one] using integrable_moment_Icc hfi 1) s
  have hfun : (fun s : ℝ => ∫ t in a..b, f t*Complex.exp (Complex.I*Real.pi*(t:ℂ)*s)) =
      spectral (volume.restrict (Icc a b)) f :=
    funext (interval_spectral_eq f hab)
  rw [hfun]
  convert hder using 1
  rw [interval_spectral_eq _ hab]
  congr 1
  funext t
  push_cast
  ring

noncomputable def basisMoment (sec : Bool) (n ell : ℕ) (s : ℝ) : ℝ :=
  (∑ j ∈ Finset.range 6, ∫ t in (j:ℝ)/6..((j:ℝ)+1)/6,
    (if sec then v n j t else u n j t) * (Complex.I*Real.pi*(t:ℂ))^ell *
      Complex.exp (Complex.I*Real.pi*(t:ℂ)*s)).re

lemma basisMoment_zero (sec : Bool) (n : ℕ) : basisMoment sec n 0 =
    if sec then foldedV n else foldedU n := by
  cases sec <;> funext s <;> simp [basisMoment,foldedU,foldedV]

lemma basisMoment_hasDerivAt (sec : Bool) (n ell : ℕ) (s : ℝ) :
    HasDerivAt (basisMoment sec n ell) (basisMoment sec n (ell+1) s) s := by
  have hd (j : ℕ) : HasDerivAt (fun s : ℝ => ∫ t in (j:ℝ)/6..((j:ℝ)+1)/6,
      (if sec then v n j t else u n j t) * (Complex.I*Real.pi*(t:ℂ))^ell *
        Complex.exp (Complex.I*Real.pi*(t:ℂ)*s))
      (∫ t in (j:ℝ)/6..((j:ℝ)+1)/6,
        (if sec then v n j t else u n j t) * (Complex.I*Real.pi*(t:ℂ))^(ell+1) *
          Complex.exp (Complex.I*Real.pi*(t:ℂ)*s)) s := by
    convert interval_exponential_hasDerivAt (by linarith : (j:ℝ)/6 ≤ ((j:ℝ)+1)/6)
      (f:=fun t => (if sec then v n j t else u n j t)*(Complex.I*Real.pi*(t:ℂ))^ell)
      (by cases sec <;> apply Continuous.continuousOn <;>
        apply Continuous.mul <;> first | exact continuous_u n j | exact continuous_v n j | fun_prop) s using 1
    congr 1
    funext t
    rw [pow_succ]
    ring
  exact Complex.reCLM.hasFDerivAt.comp_hasDerivAt s
    (HasDerivAt.fun_sum (fun j (_ : j ∈ Finset.range 6) => hd j))

lemma basisU_factor (n : ℕ) (hn : n%12 ∈ residues) (s : ℝ) :
    (s-n)^2*basisMoment false n 0 s = P s := by
  have hz := (Pmoment_node_data n hn).1
  rw [Pmoment_zero] at hz
  rw [basisMoment_zero]
  simp only [Bool.false_eq_true,ite_false]
  by_cases hs : s = n
  · simp [hs,hz]
  · rw [(folded_basis_quotients n hn s hs).1]
    field_simp

lemma basisV_factor (n : ℕ) (hn : n%12 ∈ residues) (s : ℝ) :
    (s-n)*basisMoment true n 0 s = P s := by
  have hz := (Pmoment_node_data n hn).1
  rw [Pmoment_zero] at hz
  rw [basisMoment_zero]
  simp only [ite_true]
  by_cases hs : s = n
  · simp [hs,hz]
  · rw [(folded_basis_quotients n hn s hs).2]
    field_simp


lemma P_hasDerivAt (s : ℝ) : HasDerivAt P (Pmoment 1 s) s := by
  simpa only [show Pmoment 0 = P from funext Pmoment_zero] using Pmoment_hasDerivAt 0 s

lemma basisU_factor_deriv1 (n : ℕ) (hn : n%12 ∈ residues) (s : ℝ) :
    2*(s-n)*basisMoment false n 0 s + (s-n)^2*basisMoment false n 1 s = Pmoment 1 s := by
  have hd := (((hasDerivAt_id s).sub_const (n:ℝ)).pow 2).mul
    (basisMoment_hasDerivAt false n 0 s)
  have heq : (fun s : ℝ => (s-n)^2*basisMoment false n 0 s) = P :=
    funext (basisU_factor n hn)
  simp only [Pi.mul_def, Pi.pow_def, id_eq] at hd
  rw [heq] at hd
  convert hd.unique (P_hasDerivAt s) using 1; simp

lemma basisU_factor_deriv2 (n : ℕ) (hn : n%12 ∈ residues) (s : ℝ) :
    2*basisMoment false n 0 s + 4*(s-n)*basisMoment false n 1 s +
      (s-n)^2*basisMoment false n 2 s = Pmoment 2 s := by
  have hl := (hasDerivAt_id s).sub_const (n:ℝ)
  have hd := ((hl.const_mul 2).mul (basisMoment_hasDerivAt false n 0 s)).add
    ((hl.pow 2).mul (basisMoment_hasDerivAt false n 1 s))
  have heq : (fun s : ℝ => 2*(s-n)*basisMoment false n 0 s +
      (s-n)^2*basisMoment false n 1 s) = Pmoment 1 := funext (basisU_factor_deriv1 n hn)
  simp only [Pi.mul_def, Pi.pow_def, Pi.add_def, id_eq] at hd
  rw [heq] at hd
  convert hd.unique (Pmoment_hasDerivAt 1 s) using 1; simp; ring

lemma basisU_factor_deriv3 (n : ℕ) (hn : n%12 ∈ residues) (s : ℝ) :
    6*basisMoment false n 1 s + 6*(s-n)*basisMoment false n 2 s +
      (s-n)^2*basisMoment false n 3 s = Pmoment 3 s := by
  have hl := (hasDerivAt_id s).sub_const (n:ℝ)
  have hd := (((basisMoment_hasDerivAt false n 0 s).const_mul 2).add
    ((hl.const_mul 4).mul (basisMoment_hasDerivAt false n 1 s))).add
    ((hl.pow 2).mul (basisMoment_hasDerivAt false n 2 s))
  have heq : (fun s : ℝ => 2*basisMoment false n 0 s +
      4*(s-n)*basisMoment false n 1 s+(s-n)^2*basisMoment false n 2 s) = Pmoment 2 :=
    funext (basisU_factor_deriv2 n hn)
  simp only [Pi.mul_def, Pi.pow_def, Pi.add_def, id_eq] at hd
  rw [heq] at hd
  convert hd.unique (Pmoment_hasDerivAt 2 s) using 1; simp; ring

lemma basisV_factor_deriv1 (n : ℕ) (hn : n%12 ∈ residues) (s : ℝ) :
    basisMoment true n 0 s + (s-n)*basisMoment true n 1 s = Pmoment 1 s := by
  have hd := ((hasDerivAt_id s).sub_const (n:ℝ)).mul (basisMoment_hasDerivAt true n 0 s)
  have heq : (fun s : ℝ => (s-n)*basisMoment true n 0 s) = P :=
    funext (basisV_factor n hn)
  simp only [Pi.mul_def, id_eq] at hd
  rw [heq] at hd
  convert hd.unique (P_hasDerivAt s) using 1; simp

lemma basisV_factor_deriv2 (n : ℕ) (hn : n%12 ∈ residues) (s : ℝ) :
    2*basisMoment true n 1 s + (s-n)*basisMoment true n 2 s = Pmoment 2 s := by
  have hd := (basisMoment_hasDerivAt true n 0 s).add
    (((hasDerivAt_id s).sub_const (n:ℝ)).mul (basisMoment_hasDerivAt true n 1 s))
  have heq : (fun s : ℝ => basisMoment true n 0 s +
      (s-n)*basisMoment true n 1 s) = Pmoment 1 := funext (basisV_factor_deriv1 n hn)
  simp only [Pi.mul_def, Pi.add_def, id_eq] at hd
  rw [heq] at hd
  convert hd.unique (Pmoment_hasDerivAt 1 s) using 1; simp; ring


theorem basis_diagonal_jets (n : ℕ) (hn : n%12 ∈ residues) :
    basisMoment false n 0 n = Q n ∧ basisMoment false n 1 n = Q n*D n ∧
    basisMoment true n 0 n = 0 ∧ basisMoment true n 1 n = Q n := by
  obtain ⟨h0,h1,h2,h3⟩ := Pmoment_node_data n hn
  have hu0 := basisU_factor_deriv2 n hn n
  have hu1 := basisU_factor_deriv3 n hn n
  have hv0 := basisV_factor_deriv1 n hn n
  have hv1 := basisV_factor_deriv2 n hn n
  simp only [sub_self,zero_mul,zero_pow (by omega : 2 ≠ 0),add_zero] at hu0 hu1 hv0 hv1
  rw [h1] at hv0
  exact ⟨by linarith,by linarith,hv0,by linarith⟩


theorem basis_off_diagonal_jets (n m : ℕ) (hn : n%12 ∈ residues)
    (hm : m%12 ∈ residues) (hnm : m ≠ n) :
    basisMoment false n 0 m = 0 ∧ basisMoment false n 1 m = 0 ∧
    basisMoment true n 0 m = 0 ∧ basisMoment true n 1 m = 0 := by
  obtain ⟨h0,h1,h2,h3⟩ := Pmoment_node_data m hm
  rw [Pmoment_zero] at h0
  have hsub : (m:ℝ)-(n:ℝ) ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hnm)
  have hu0 := basisU_factor n hn m
  have hv0 := basisV_factor n hn m
  rw [h0] at hu0 hv0
  have hu : basisMoment false n 0 m = 0 := (mul_eq_zero.mp hu0).resolve_left (pow_ne_zero 2 hsub)
  have hv : basisMoment true n 0 m = 0 := (mul_eq_zero.mp hv0).resolve_left hsub
  have hu1 := basisU_factor_deriv1 n hn m
  have hv1 := basisV_factor_deriv1 n hn m
  rw [hu,h1,mul_zero,zero_add] at hu1
  rw [hv,h1,zero_add] at hv1
  exact ⟨hu,(mul_eq_zero.mp hu1).resolve_left (pow_ne_zero 2 hsub),
    hv,(mul_eq_zero.mp hv1).resolve_left hsub⟩

end SharpPlanar

namespace SharpPlanar
open MeasureTheory Set

lemma realSpectral_norm (ell : ℕ) {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) (s : ℝ) :
    ‖(Complex.I*Real.pi*(t:ℂ))^ell * Complex.exp (Complex.I*Real.pi*(t:ℂ)*s)‖ ≤ Real.pi^ell := by
  have he : ‖Complex.exp (Complex.I*Real.pi*(t:ℂ)*s)‖ = 1 := by
    rw [Complex.norm_exp]
    simp
  rw [norm_mul, norm_pow, he, mul_one]
  apply pow_le_pow_left₀ (norm_nonneg _)
  rw [norm_mul,norm_mul,Complex.norm_I,one_mul,Complex.norm_real,Complex.norm_real,
    Real.norm_eq_abs,Real.norm_eq_abs,abs_of_pos Real.pi_pos,abs_of_nonneg ht.1]
  exact mul_le_of_le_one_right Real.pi_pos.le ht.2

lemma basisMoment_bound (sec : Bool) (n ell : ℕ) (s : ℝ) :
    |basisMoment sec n ell s| ≤ densityBound * Real.pi^ell := by
  have hj (j : ℕ) (hj : j < 6) :
      ‖∫ t in (j:ℝ)/6..((j:ℝ)+1)/6,
        (if sec then v n j t else u n j t) * (Complex.I*Real.pi*(t:ℂ))^ell *
          Complex.exp (Complex.I*Real.pi*(t:ℂ)*s)‖ ≤ densityBound*Real.pi^ell/6 := by
    have hh := intervalIntegral.norm_integral_le_of_norm_le_const
      (f:=fun t => (if sec then v n j t else u n j t) * (Complex.I*Real.pi*(t:ℂ))^ell *
        Complex.exp (Complex.I*Real.pi*(t:ℂ)*s))
      (a:=(j:ℝ)/6) (b:=((j:ℝ)+1)/6) (C:=densityBound*Real.pi^ell) (fun t ht => ?_)
    · convert hh using 1
      rw [show ((j:ℝ)+1)/6-(j:ℝ)/6=1/6 by ring,abs_of_pos (by norm_num : (0:ℝ)<1/6)]
      ring
    · rw [mul_assoc,norm_mul]
      apply mul_le_mul _ (realSpectral_norm ell (piece_interval hj (uIoc_subset_uIcc ht)) s)
        (norm_nonneg _) densityBound_nonneg
      cases sec
      · exact u_bound n j (piece_interval hj (uIoc_subset_uIcc ht))
      · exact v_bound' n j (piece_interval hj (uIoc_subset_uIcc ht))
  unfold basisMoment
  calc
    _ ≤ ‖∑ j ∈ Finset.range 6, ∫ t in (j:ℝ)/6..((j:ℝ)+1)/6,
        (if sec then v n j t else u n j t) * (Complex.I*Real.pi*(t:ℂ))^ell *
          Complex.exp (Complex.I*Real.pi*(t:ℂ)*s)‖ := Complex.abs_re_le_norm _
    _ ≤ ∑ j ∈ Finset.range 6, ‖∫ t in (j:ℝ)/6..((j:ℝ)+1)/6,
        (if sec then v n j t else u n j t) * (Complex.I*Real.pi*(t:ℂ))^ell *
          Complex.exp (Complex.I*Real.pi*(t:ℂ)*s)‖ := norm_sum_le _ _
    _ ≤ ∑ j ∈ Finset.range 6, densityBound*Real.pi^ell/6 := by
      exact Finset.sum_le_sum (fun j hj' => hj j (Finset.mem_range.mp hj'))
    _ = _ := by simp; ring

noncomputable def cardinalSeries (p : CardinalData) (ell : ℕ) (s : ℝ) : ℝ :=
  p.C*Pmoment ell s + p.c₀*basisMoment false 0 ell s + p.d₀*basisMoment true 0 ell s +
    ∑' n : Node, (p.x (n,false)*basisMoment false n.val ell s +
      p.x (n,true)*basisMoment true n.val ell s)

lemma cardinalSeries_summand_bound (p : CardinalData) (ell : ℕ) (s : ℝ) (n : Node) :
    ‖p.x (n,false)*basisMoment false n.val ell s +
      p.x (n,true)*basisMoment true n.val ell s‖ ≤
      (densityBound*Real.pi^ell)*(|p.x (n,false)|+|p.x (n,true)|) := by
  calc
    _ ≤ ‖p.x (n,false)*basisMoment false n.val ell s‖ +
        ‖p.x (n,true)*basisMoment true n.val ell s‖ := norm_add_le _ _
    _ = |p.x (n,false)| * |basisMoment false n.val ell s| +
        |p.x (n,true)| * |basisMoment true n.val ell s| := by simp [norm_mul,Real.norm_eq_abs]
    _ ≤ |p.x (n,false)| * (densityBound*Real.pi^ell)+
        |p.x (n,true)| * (densityBound*Real.pi^ell) := by
      gcongr <;> apply basisMoment_bound
    _ = _ := by ring

lemma cardinalSeries_summable (p : CardinalData) (ell : ℕ) (s : ℝ) :
    Summable (fun n : Node => p.x (n,false)*basisMoment false n.val ell s +
      p.x (n,true)*basisMoment true n.val ell s) :=
  ((X_summable_pairs p.x).mul_left (densityBound*Real.pi^ell)).of_norm_bounded
    (cardinalSeries_summand_bound p ell s)

lemma cardinalSeries_hasDerivAt (p : CardinalData) (ell : ℕ) (s : ℝ) :
    HasDerivAt (cardinalSeries p ell) (cardinalSeries p (ell+1) s) s := by
  have hsum := hasDerivAt_tsum
    ((X_summable_pairs p.x).mul_left (densityBound*Real.pi^(ell+1)))
    (fun n y => ((basisMoment_hasDerivAt false n.val ell y).const_mul (p.x (n,false))).add
      ((basisMoment_hasDerivAt true n.val ell y).const_mul (p.x (n,true))))
    (fun n y => cardinalSeries_summand_bound p (ell+1) y n)
    (cardinalSeries_summable p ell 0) s
  exact ((((Pmoment_hasDerivAt ell s).const_mul p.C).add
    ((basisMoment_hasDerivAt false 0 ell s).const_mul p.c₀)).add
    ((basisMoment_hasDerivAt true 0 ell s).const_mul p.d₀)).add hsum


lemma cardinalSeries_jets (p : CardinalData) (m : Node) :
    cardinalSeries p 0 m.val = Q m.val * p.x (m,false) ∧
    cardinalSeries p 1 m.val = Q m.val * (D m.val*p.x (m,false)+p.x (m,true)) := by
  obtain ⟨hP0,hP1,-,-⟩ := Pmoment_node_data m.val m.property.2
  obtain ⟨hU0,hU1,hV0,hV1⟩ := basis_diagonal_jets m.val m.property.2
  have hm : m.val ≠ 0 := Nat.ne_of_gt m.property.1
  have hz : 0%12 ∈ residues := by norm_num [residues]
  obtain ⟨hc0,hc1,hd0,hd1⟩ := basis_off_diagonal_jets 0 m.val hz m.property.2 hm
  have hother (n : Node) (hn : n ≠ m) :
      basisMoment false n.val 0 m.val = 0 ∧ basisMoment false n.val 1 m.val = 0 ∧
      basisMoment true n.val 0 m.val = 0 ∧ basisMoment true n.val 1 m.val = 0 := by
    apply basis_off_diagonal_jets n.val m.val n.property.2 m.property.2
    intro he
    exact hn (Subtype.ext he.symm)
  have hs0 : (∑' n : Node, (p.x (n,false)*basisMoment false n.val 0 m.val +
      p.x (n,true)*basisMoment true n.val 0 m.val)) = p.x (m,false)*Q m.val := by
    rw [tsum_eq_single m]
    · rw [hU0,hV0]; ring
    · intro n hn
      obtain ⟨h0,h1,h2,h3⟩ := hother n hn
      simp [h0,h2]
  have hs1 : (∑' n : Node, (p.x (n,false)*basisMoment false n.val 1 m.val +
      p.x (n,true)*basisMoment true n.val 1 m.val)) =
      p.x (m,false)*(Q m.val*D m.val)+p.x (m,true)*Q m.val := by
    rw [tsum_eq_single m]
    · rw [hU1,hV1]
    · intro n hn
      obtain ⟨h0,h1,h2,h3⟩ := hother n hn
      simp [h1,h3]
  constructor
  · simp only [cardinalSeries,hP0,hc0,hd0,hs0,mul_zero,zero_add]
    ring
  · simp only [cardinalSeries,hP1,hc1,hd1,hs1,mul_zero,zero_add]
    ring

lemma cardinalSeries_origin_jets (p : CardinalData) :
    cardinalSeries p 0 0 = Q 0 * p.c₀ ∧
    cardinalSeries p 1 0 = Q 0 * (D 0*p.c₀+p.d₀) := by
  have hz : 0%12 ∈ residues := by norm_num [residues]
  obtain ⟨hP0,hP1,-,-⟩ := Pmoment_node_data 0 hz
  obtain ⟨hU0,hU1,hV0,hV1⟩ := basis_diagonal_jets 0 hz
  simp only [Nat.cast_zero] at hP0 hP1 hU0 hU1 hV0 hV1
  have ha (n : Node) :
      basisMoment false n.val 0 0 = 0 ∧ basisMoment false n.val 1 0 = 0 ∧
      basisMoment true n.val 0 0 = 0 ∧ basisMoment true n.val 1 0 = 0 := by
    simpa only [Nat.cast_zero] using basis_off_diagonal_jets n.val 0 n.property.2 hz (Nat.ne_of_lt n.property.1)
  have hs0 : (∑' n : Node, (p.x (n,false)*basisMoment false n.val 0 0 +
      p.x (n,true)*basisMoment true n.val 0 0)) = 0 := by
    convert (tsum_zero : (∑' _ : Node, (0:ℝ)) = 0) using 1
    apply tsum_congr
    intro n
    simp [(ha n).1,(ha n).2.2.1]
  have hs1 : (∑' n : Node, (p.x (n,false)*basisMoment false n.val 1 0 +
      p.x (n,true)*basisMoment true n.val 1 0)) = 0 := by
    convert (tsum_zero : (∑' _ : Node, (0:ℝ)) = 0) using 1
    apply tsum_congr
    intro n
    simp [(ha n).2.1,(ha n).2.2.2]
  constructor
  · simp only [cardinalSeries,hP0,hU0,hV0,hs0,mul_zero,zero_add,add_zero]
    ring
  · simp only [cardinalSeries,hP1,hU1,hV1,hs1,mul_zero,zero_add,add_zero]
    ring

end SharpPlanar

namespace SharpPlanar
open MeasureTheory Set

lemma interval_integral_tsum_uniform {ι : Type*} [Countable ι]
    {f : ι → ℝ → ℂ} {a b : ℝ} (hab : a ≤ b)
    (hf : ∀ i, ContinuousOn (f i) (Icc a b))
    (g : ι → ℝ) (hg : Summable g)
    (hbound : ∀ i t, t ∈ Icc a b → ‖f i t‖ ≤ g i) :
    (∫ t in a..b, ∑' i, f i t) = ∑' i, ∫ t in a..b, f i t := by
  have hi (i : ι) : IntegrableOn (f i) (Icc a b) volume := (hf i).integrableOn_Icc
  have hb (i : ι) : ‖∫ t in Icc a b, ‖f i t‖‖ ≤ |b-a| *g i := by
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab]
    calc
      _ ≤ g i * |b-a| := intervalIntegral.norm_integral_le_of_norm_le_const
        (fun t ht => by simpa using hbound i t (uIcc_of_le hab ▸ uIoc_subset_uIcc ht))
      _ = _ := mul_comm _ _
  have hs : Summable (fun i => ∫ t in Icc a b, ‖f i t‖) :=
    (hg.mul_left |b-a|).of_norm_bounded hb
  simp_rw [intervalIntegral.integral_of_le hab, ← integral_Icc_eq_integral_Ioc]
  exact (integral_tsum_of_summable_integral_norm hi hs).symm

noncomputable def directKernel (ell : ℕ) (s t : ℝ) : ℂ :=
  (Complex.I*Real.pi*(t:ℂ))^ell * Complex.exp (Complex.I*Real.pi*(t:ℂ)*s)

lemma continuous_directKernel (ell : ℕ) (s : ℝ) : Continuous (directKernel ell s) := by
  unfold directKernel
  fun_prop

lemma directDensity_tsum (x : X) (ell j : ℕ) (hj : j < 6) (s : ℝ) :
    (∫ t in (j:ℝ)/6..((j:ℝ)+1)/6, density (positiveData x) j t * directKernel ell s t) =
      ∑' n : Node, ∫ t in (j:ℝ)/6..((j:ℝ)+1)/6,
        ((x (n,false):ℂ)*u n.val j t + (x (n,true):ℂ)*v n.val j t) * directKernel ell s t := by
  have he (t : ℝ) : density (positiveData x) j t * directKernel ell s t =
      ∑' n : Node, ((x (n,false):ℂ)*u n.val j t + (x (n,true):ℂ)*v n.val j t) * directKernel ell s t := by
    simp only [density,positiveData,Complex.ofReal_zero,zero_mul,zero_add,tsum_mul_right]
  simp_rw [he]
  apply interval_integral_tsum_uniform (by linarith : (j:ℝ)/6 ≤ ((j:ℝ)+1)/6)
    (fun n => by apply Continuous.continuousOn; apply Continuous.mul
                 · exact (continuous_const.mul (continuous_u n.val j)).add
                     (continuous_const.mul (continuous_v n.val j))
                 · exact continuous_directKernel ell s)
    (fun n : Node => (densityBound*Real.pi^ell)*(|x (n,false)|+|x (n,true)|))
    ((X_summable_pairs x).mul_left (densityBound*Real.pi^ell))
  intro n t ht
  rw [norm_mul]
  have ht' := piece_interval hj (show t ∈ uIcc ((j:ℝ)/6) (((j:ℝ)+1)/6) by
    rwa [uIcc_of_le (by linarith : (j:ℝ)/6 ≤ ((j:ℝ)+1)/6)])
  calc
    _ ≤ (densityBound*(|x (n,false)|+|x (n,true)|))*Real.pi^ell :=
      mul_le_mul (summand_bound x n j ht') (realSpectral_norm ell ht' s)
        (norm_nonneg _) (mul_nonneg densityBound_nonneg (add_nonneg (abs_nonneg _) (abs_nonneg _)))
    _ = _ := by ring

end SharpPlanar

namespace SharpPlanar
open MeasureTheory Set

lemma direct_piece_integrable (p : CardinalData) (ell j : ℕ) (hj : j < 6) (s : ℝ) :
    IntervalIntegrable (fun t => density p j t * directKernel ell s t) volume
      ((j:ℝ)/6) (((j:ℝ)+1)/6) := by
  exact ((continuousOn_density p j).mul (continuous_directKernel ell s).continuousOn).mono
    (fun _ ht => piece_interval hj ht) |>.intervalIntegrable

lemma basis_piece_integrable (sec : Bool) (n ell j : ℕ) (s : ℝ) :
    IntervalIntegrable (fun t => (if sec then v n j t else u n j t) * directKernel ell s t) volume
      ((j:ℝ)/6) (((j:ℝ)+1)/6) := by
  apply Continuous.intervalIntegrable
  cases sec
  · exact (continuous_u n j).mul (continuous_directKernel ell s)
  · exact (continuous_v n j).mul (continuous_directKernel ell s)

lemma direct_basis_pair (c d : ℝ) (n ell j : ℕ) (s : ℝ) :
    (∫ t in (j:ℝ)/6..((j:ℝ)+1)/6,
      ((c:ℂ)*u n j t+(d:ℂ)*v n j t)*directKernel ell s t) =
    (c:ℂ)*(∫ t in (j:ℝ)/6..((j:ℝ)+1)/6,u n j t*directKernel ell s t) +
    (d:ℂ)*(∫ t in (j:ℝ)/6..((j:ℝ)+1)/6,v n j t*directKernel ell s t) := by
  simp_rw [add_mul,mul_assoc]
  have hU : IntervalIntegrable (fun t => u n j t * directKernel ell s t) volume
      ((j:ℝ)/6) (((j:ℝ)+1)/6) := by simpa using basis_piece_integrable false n ell j s
  have hV : IntervalIntegrable (fun t => v n j t * directKernel ell s t) volume
      ((j:ℝ)/6) (((j:ℝ)+1)/6) := by simpa using basis_piece_integrable true n ell j s
  rw [intervalIntegral.integral_add (hU.const_mul (c:ℂ)) (hV.const_mul (d:ℂ)),
    intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul]

lemma direct_basis_integral_bound (x : X) (n : Node) (ell j : ℕ) (hj : j < 6) (s : ℝ) :
    ‖∫ t in (j:ℝ)/6..((j:ℝ)+1)/6,
      ((x (n,false):ℂ)*u n.val j t+(x (n,true):ℂ)*v n.val j t)*directKernel ell s t‖ ≤
        ((densityBound*Real.pi^ell)/6)*(|x (n,false)|+|x (n,true)|) := by
  have hh := intervalIntegral.norm_integral_le_of_norm_le_const
    (f:=fun t => ((x (n,false):ℂ)*u n.val j t+(x (n,true):ℂ)*v n.val j t)*directKernel ell s t)
    (a:=(j:ℝ)/6) (b:=((j:ℝ)+1)/6)
    (C:=(densityBound*Real.pi^ell)*(|x (n,false)|+|x (n,true)|)) (fun t ht => ?_)
  · convert hh using 1
    rw [show ((j:ℝ)+1)/6-(j:ℝ)/6=1/6 by ring,abs_of_pos (by norm_num : (0:ℝ)<1/6)]
    ring
  · rw [norm_mul]
    have ht' := piece_interval hj (uIoc_subset_uIcc ht)
    calc
      _ ≤ (densityBound*(|x (n,false)|+|x (n,true)|))*Real.pi^ell :=
        mul_le_mul (summand_bound x n j ht') (realSpectral_norm ell ht' s)
          (norm_nonneg _) (mul_nonneg densityBound_nonneg (add_nonneg (abs_nonneg _) (abs_nonneg _)))
      _ = _ := by ring

lemma direct_basis_integral_summable (x : X) (ell j : ℕ) (hj : j < 6) (s : ℝ) :
    Summable (fun n : Node => ∫ t in (j:ℝ)/6..((j:ℝ)+1)/6,
      ((x (n,false):ℂ)*u n.val j t+(x (n,true):ℂ)*v n.val j t)*directKernel ell s t) :=
  ((X_summable_pairs x).mul_left ((densityBound*Real.pi^ell)/6)).of_norm_bounded
    (fun n => direct_basis_integral_bound x n ell j hj s)

lemma direct_positive_series (x : X) (ell : ℕ) (s : ℝ) :
    (∑ j ∈ Finset.range 6, ∫ t in (j:ℝ)/6..((j:ℝ)+1)/6,
      density (positiveData x) j t * directKernel ell s t).re =
    ∑' n : Node, (x (n,false)*basisMoment false n.val ell s +
      x (n,true)*basisMoment true n.val ell s) := by
  have he (j : ℕ) (hj : j ∈ Finset.range 6) := directDensity_tsum x ell j (Finset.mem_range.mp hj) s
  conv_lhs => arg 1; rw [Finset.sum_congr rfl he]
  rw [← Summable.tsum_finsetSum (fun j hj => direct_basis_integral_summable x ell j (Finset.mem_range.mp hj) s)]
  change Complex.reCLM (∑' n : Node, ∑ j ∈ Finset.range 6, ∫ t in (j:ℝ)/6..((j:ℝ)+1)/6,
    ((x (n,false):ℂ)*u n.val j t+(x (n,true):ℂ)*v n.val j t)*directKernel ell s t) = _
  rw [ContinuousLinearMap.map_tsum _ (summable_sum
    (fun j hj => direct_basis_integral_summable x ell j (Finset.mem_range.mp hj) s))]
  apply tsum_congr
  intro n
  simp_rw [direct_basis_pair]
  simp only [Finset.sum_add_distrib,← Finset.mul_sum,
    Complex.reCLM_apply,Complex.add_re,
    Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
  simp [basisMoment,directKernel,mul_assoc]

end SharpPlanar


open Set Filter MeasureTheory Asymptotics
open scoped Topology ContDiff SchwartzMap

namespace SharpPlanar

noncomputable def expCut (c x : ℝ) : ℝ :=
  Real.smoothTransition (x+1) * Real.exp (-c*x)

lemma expCut_smooth (c : ℝ) : ContDiff ℝ ∞ (expCut c) := by
  unfold expCut
  fun_prop

lemma expCut_eq (c x : ℝ) (hx : 0 ≤ x) : expCut c x = Real.exp (-c*x) := by
  simp [expCut, Real.smoothTransition.one_of_one_le (by linarith : 1 ≤ x+1)]

lemma expCut_zero (c x : ℝ) (hx : x ≤ -1) : expCut c x = 0 := by
  simp [expCut, Real.smoothTransition.zero_of_nonpos (by linarith : x+1 ≤ 0)]

lemma iteratedDeriv_expCut_pos (c : ℝ) (n : ℕ) {x : ℝ} (hx : 0 < x) :
    iteratedDeriv n (expCut c) x = (-c)^n * Real.exp (-c*x) := by
  have he : expCut c =ᶠ[𝓝 x] (fun y => Real.exp (-c*y)) := by
    filter_upwards [eventually_gt_nhds hx] with y hy
    exact expCut_eq c y hy.le
  rw [he.iteratedDeriv_eq n, iteratedDeriv_exp_const_mul]

lemma iteratedDeriv_expCut_neg (c : ℝ) (n : ℕ) {x : ℝ} (hx : x < -1) :
    iteratedDeriv n (expCut c) x = 0 := by
  have he : expCut c =ᶠ[𝓝 x] (fun _ => (0 : ℝ)) := by
    filter_upwards [eventually_lt_nhds hx] with y hy
    exact expCut_zero c y hy.le
  rw [he.iteratedDeriv_eq n]
  simp

lemma expCut_decay (c : ℝ) (hc : 0 < c) (k n : ℕ) :
    ∃ C : ℝ, ∀ x, ‖x‖^k * ‖iteratedFDeriv ℝ n (expCut c) x‖ ≤ C := by
  let g : ℝ → ℝ := fun x => ‖x‖^k * ‖iteratedDeriv n (expCut c) x‖
  have hg : Continuous g := by
    exact (continuous_norm.pow k).mul
      (((expCut_smooth c).continuous_iteratedDeriv n (by exact_mod_cast (le_top : (n : ℕ∞) ≤ ⊤))).norm)
  have ht : Tendsto g atTop (𝓝 0) := by
    have he : g =ᶠ[atTop] (fun x : ℝ => (x^(k : ℝ) * Real.exp (-c*x)) * ‖(-c)^n‖) := by
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
      change ‖x‖^k * ‖iteratedDeriv n (expCut c) x‖ = _
      rw [iteratedDeriv_expCut_pos c n hx, norm_mul]
      simp only [Real.norm_eq_abs, abs_of_pos hx, Real.rpow_natCast, Real.abs_exp]
      ring
    apply Tendsto.congr' he.symm
    simpa using (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (k : ℝ) c hc).mul_const ‖(-c)^n‖
  have hb : Tendsto g atBot (𝓝 0) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_lt_atBot (-1 : ℝ)] with x hx
    simp [g, iteratedDeriv_expCut_neg c n hx]
  have hbd := hg.isBounded_range_iff_isBigO_atTop_atBot.mpr
    ⟨ht.isBigO_one ℝ, hb.isBigO_one ℝ⟩
  obtain ⟨C, hC⟩ := hbd.exists_norm_le
  refine ⟨C, fun x => ?_⟩
  have hx := hC (g x) (mem_range_self x)
  simpa only [g, norm_iteratedFDeriv_eq_norm_iteratedDeriv,
    Real.norm_eq_abs, abs_mul, abs_pow, abs_abs, norm_norm] using hx

noncomputable def expCutSchwartz (c : ℝ) (hc : 0 < c) : SchwartzMap ℝ ℝ where
  toFun := expCut c
  smooth' := expCut_smooth c
  decay' := expCut_decay c hc

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]


noncomputable def gaussianSchwartz (c : ℝ) (hc : 0 < c) : SchwartzMap E ℝ :=
  SchwartzMap.compCLM ℝ (g := fun x : E => ‖x‖^2) (Function.hasTemperateGrowth_norm_sq E)
    ⟨1, 1, fun x => by
      simp only [pow_one, one_mul, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg ‖x‖)]
      nlinarith [sq_nonneg (‖x‖-1)]⟩ (expCutSchwartz c hc)

lemma gaussianSchwartz_apply (c : ℝ) (hc : 0 < c) (x : E) :
    gaussianSchwartz c hc x = Real.exp (-c*‖x‖^2) := by
  change expCut c (‖x‖^2) = _
  exact expCut_eq c _ (sq_nonneg _)

end SharpPlanar


open scoped SchwartzMap

namespace SharpPlanar

lemma spectral_dirac_eq (t : ℝ) (c : ℂ) (s : ℝ) :
    spectral (Measure.dirac t) (fun _ => c) s =
      Complex.exp (((Real.pi*t*s : ℝ) : ℂ)*Complex.I) * c := by
  simp [spectral]

lemma spectral_dirac_temperate (t : ℝ) (c : ℂ) :
    Function.HasTemperateGrowth (spectral (Measure.dirac t) (fun _ => c)) := by
  apply spectral_temperate
  · exact integrable_dirac (by finiteness)
  · intro n
    exact integrable_dirac (by finiteness)


noncomputable def cardinal (p : CardinalData) (s : ℝ) : ℝ :=
  ((spectral (Measure.dirac 0) (fun _ => (p.C : ℂ) * Pcoeff 0) s) +
    (∑ j ∈ Finset.Icc (1 : ℕ) 6,
      spectral (Measure.dirac ((j : ℝ)/6)) (fun _ => 2*(p.C : ℂ)*Pcoeff j) s) +
    (∑ j ∈ Finset.range 6,
      spectral (volume.restrict (Set.Icc ((j : ℝ)/6) (((j : ℝ)+1)/6)))
        (density p j) s)).re

lemma cardinal_temperate (p : CardinalData) :
    Function.HasTemperateGrowth (cardinal p) := by
  have h₀ := spectral_dirac_temperate 0 ((p.C : ℂ)*Pcoeff 0)
  have h₁ : Function.HasTemperateGrowth (fun s => ∑ j ∈ Finset.Icc (1 : ℕ) 6,
      spectral (Measure.dirac ((j : ℝ)/6)) (fun _ => 2*(p.C : ℂ)*Pcoeff j) s) := by
    exact Function.HasTemperateGrowth.sum fun j _ => spectral_dirac_temperate _ _
  have h₂ : Function.HasTemperateGrowth (fun s => ∑ j ∈ Finset.range 6,
      spectral (volume.restrict (Set.Icc ((j : ℝ)/6) (((j : ℝ)+1)/6)))
        (density p j) s) := by
    apply Function.HasTemperateGrowth.sum
    intro j hj
    apply spectral_Icc_temperate
    apply ContinuousOn.integrableOn_compact isCompact_Icc
    apply (continuousOn_density p j).mono
    intro t ht
    have hj' : (j : ℝ) ≤ 5 := by exact_mod_cast (Nat.le_of_lt_succ (Finset.mem_range.mp hj))
    have hj0 : (0 : ℝ) ≤ j := by positivity
    constructor <;> linarith [ht.1, ht.2]
  exact Complex.reCLM.hasTemperateGrowth.comp ((h₀.add h₁).add h₂)


lemma radiusCoord_temperate :
    Function.HasTemperateGrowth (fun x : Plane => b*‖x‖^2) := by
  fun_prop

noncomputable def qSchwartz (p : CardinalData) : SchwartzMap Plane ℝ :=
  SchwartzMap.smulLeftCLM ℝ (fun x : Plane => cardinal p (b*‖x‖^2))
    (gaussianSchwartz (Real.pi*h*b) (mul_pos (mul_pos Real.pi_pos h_pos) b_pos))

lemma qSchwartz_apply (p : CardinalData) (x : Plane) :
    qSchwartz p x = Real.exp (-Real.pi*h*(b*‖x‖^2)) * cardinal p (b*‖x‖^2) := by
  have hq : Function.HasTemperateGrowth (fun x : Plane => cardinal p (b*‖x‖^2)) :=
    (cardinal_temperate p).comp radiusCoord_temperate
  rw [qSchwartz, SchwartzMap.smulLeftCLM_apply_apply hq, gaussianSchwartz_apply]
  simp only [smul_eq_mul]
  rw [mul_comm]
  congr 2
  ring

end SharpPlanar

namespace SharpPlanar
open MeasureTheory Set

lemma directDensity_split (p : CardinalData) (ell j : ℕ) (hj : j < 6) (s : ℝ) :
    (∫ t in (j:ℝ)/6..((j:ℝ)+1)/6, density p j t * directKernel ell s t) =
      (p.c₀:ℂ)*(∫ t in (j:ℝ)/6..((j:ℝ)+1)/6, u 0 j t * directKernel ell s t) +
      (p.d₀:ℂ)*(∫ t in (j:ℝ)/6..((j:ℝ)+1)/6, v 0 j t * directKernel ell s t) +
      (∫ t in (j:ℝ)/6..((j:ℝ)+1)/6, density (positiveData p.x) j t * directKernel ell s t) := by
  have he (t : ℝ) : density p j t * directKernel ell s t =
      ((p.c₀:ℂ)*u 0 j t+(p.d₀:ℂ)*v 0 j t)*directKernel ell s t +
      density (positiveData p.x) j t * directKernel ell s t := by
    simp [density,positiveData,add_mul]
  simp_rw [he]
  have ha : IntervalIntegrable (fun t => ((p.c₀:ℂ)*u 0 j t+(p.d₀:ℂ)*v 0 j t)*directKernel ell s t)
      volume ((j:ℝ)/6) (((j:ℝ)+1)/6) := by
    apply Continuous.intervalIntegrable
    exact ((continuous_const.mul (continuous_u 0 j)).add
      (continuous_const.mul (continuous_v 0 j))).mul (continuous_directKernel ell s)
  rw [intervalIntegral.integral_add ha (direct_piece_integrable _ ell j hj s),direct_basis_pair]

lemma directDensity_series (p : CardinalData) (ell : ℕ) (s : ℝ) :
    (∑ j ∈ Finset.range 6, ∫ t in (j:ℝ)/6..((j:ℝ)+1)/6,
      density p j t * directKernel ell s t).re =
    p.c₀*basisMoment false 0 ell s + p.d₀*basisMoment true 0 ell s +
      ∑' n : Node, (p.x (n,false)*basisMoment false n.val ell s +
        p.x (n,true)*basisMoment true n.val ell s) := by
  have he (j : ℕ) (hj : j ∈ Finset.range 6) := directDensity_split p ell j (Finset.mem_range.mp hj) s
  conv_lhs => arg 1; rw [Finset.sum_congr rfl he]
  simp only [Finset.sum_add_distrib,← Finset.mul_sum,Complex.add_re,
    Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
  rw [direct_positive_series]
  simp only [basisMoment,Bool.false_eq_true,ite_false,ite_true,directKernel,mul_assoc]

lemma spectral_interval_direct (p : CardinalData) (j : ℕ) (s : ℝ) :
    spectral (volume.restrict (Icc ((j:ℝ)/6) (((j:ℝ)+1)/6))) (density p j) s =
    ∫ t in (j:ℝ)/6..((j:ℝ)+1)/6, density p j t * directKernel 0 s t := by
  rw [spectral,integral_Icc_eq_integral_Ioc,← intervalIntegral.integral_of_le
    (by linarith : (j:ℝ)/6 ≤ ((j:ℝ)+1)/6)]
  apply intervalIntegral.integral_congr
  intro t _
  simp only [directKernel,pow_zero,one_mul]
  rw [mul_comm]
  congr 2
  push_cast
  ring

lemma cardinal_eq_cardinalSeries (p : CardinalData) (s : ℝ) :
    cardinal p s = cardinalSeries p 0 s := by
  unfold cardinal
  simp_rw [spectral_dirac_eq,spectral_interval_direct]
  have hat : (Complex.exp (((Real.pi*0*s:ℝ):ℂ)*Complex.I)*((p.C:ℂ)*Pcoeff 0) +
      ∑ j ∈ Finset.Icc (1:ℕ) 6,
        Complex.exp (((Real.pi*((j:ℝ)/6)*s:ℝ):ℂ)*Complex.I)*(2*(p.C:ℂ)*Pcoeff j)) =
      (p.C:ℂ)*(Pcoeff 0 + ∑ j ∈ Finset.Icc (1:ℕ) 6,
        2*Pcoeff j*Complex.exp (Complex.I*Real.pi*((j:ℝ)/6)*s)) := by
    simp only [mul_zero,Complex.ofReal_zero,zero_mul,Complex.exp_zero,one_mul,mul_add,Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    have he : (((Real.pi*((j:ℝ)/6)*s:ℝ):ℂ)*Complex.I) =
        Complex.I*Real.pi*((j:ℝ)/6)*s := by push_cast; ring
    rw [he]
    ring
  rw [hat,Complex.add_re,Complex.mul_re]
  simp only [Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
  rw [directDensity_series]
  simp only [cardinalSeries,Pmoment,pow_zero,mul_one]
  push_cast
  ring

lemma cardinal_hasDerivAt (p : CardinalData) (s : ℝ) :
    HasDerivAt (cardinal p) (cardinalSeries p 1 s) s := by
  simpa only [funext (cardinal_eq_cardinalSeries p)] using cardinalSeries_hasDerivAt p 0 s

lemma cardinal_jets (p : CardinalData) (m : Node) :
    cardinal p m.val = Q m.val*p.x (m,false) ∧
      deriv (cardinal p) m.val = Q m.val*(p.x (m,true)+D m.val*p.x (m,false)) := by
  rcases cardinalSeries_jets p m with ⟨h0,h1⟩
  rw [cardinal_eq_cardinalSeries,h0,(cardinal_hasDerivAt p m.val).deriv]
  exact ⟨rfl,by simpa only [add_comm] using h1⟩

end SharpPlanar

end OAI
