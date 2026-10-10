import Mathlib

namespace OAI

/-! Hyperbolic integral transforms, their domination estimates, and derivatives.

The development follows OpenAI, *Uniform marked-polygon estimates and sharp finite bridge moments*
(2026), Sections 6 and 7. -/

section
namespace CriticalHoneycomb.FiniteFunctional.Analytic
open Real Complex Filter Topology
lemma real_unit_mem_integerComplement {x : ℝ} (h0 : 0<x) (h1 : x<1) :
    (x:ℂ)∈integerComplement := by
  rw [mem_integerComplement_iff]
  rintro ⟨n,hn⟩
  have he : (n:ℝ)=x := by exact_mod_cast hn
  have hnp : 0<n := by exact_mod_cast (show (0:ℝ)<n by linarith)
  have hnl : n<1 := by exact_mod_cast (show (n:ℝ)<1 by linarith)
  omega
lemma cot_sum_real {x : ℝ} (h0 : 0<x) (h1 : x<1) :
    HasSum (fun n : ℕ=>1/(x-(n+1))+1/(x+(n+1)))
      (Real.pi*(Real.tan (Real.pi*x))⁻¹-1/x) := by
  have hx:=real_unit_mem_integerComplement h0 h1
  have hs:=(summable_cotTerm hx).hasSum
  rw [←cot_series_rep' hx] at hs
  have hr:=Complex.hasSum_re hs
  simpa only [cotTerm,Complex.cot,Real.tan_eq_sin_div_cos,inv_div,←Complex.ofReal_cos,←Complex.ofReal_sin,←Complex.ofReal_natCast,←Complex.ofReal_one,
    ←Complex.ofReal_add,←Complex.ofReal_sub,←Complex.ofReal_div,←Complex.ofReal_mul,
    ←Complex.ofReal_tan,←Complex.ofReal_inv,Complex.ofReal_re,one_div] using hr
lemma shifted_reciprocal_sums (x : ℝ) (m : ℕ) :
    (∑ n∈Finset.range m,(1/(x+n)+1/(x-(n+1))))=
      (∑ n∈Finset.range m,(1/(x-(n+1))+1/(x+(n+1))))+1/x-1/(x+m) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ,Finset.sum_range_succ,ih]
    push_cast
    ring
lemma positive_shifted_reciprocal_hasSum {x : ℝ} (h0 : 0<x) (hx : x≤1/2) :
    HasSum (fun n : ℕ=>1/(x+n)+1/(x-(n+1))) (Real.pi*(Real.tan (Real.pi*x))⁻¹) := by
  have h1 : x<1 := by linarith
  have hn : ∀ n : ℕ,0≤1/(x+n)+1/(x-(n+1)) := by
    intro n
    have hb : 0<x+(n:ℝ) := by positivity
    have hc : 0<(n:ℝ)+1-x := by
      have hh : (0:ℝ)≤n := by positivity
      linarith
    rw [show x-((n:ℝ)+1)=-((n:ℝ)+1-x) by ring,div_neg,←sub_eq_add_neg,sub_nonneg]
    exact one_div_le_one_div_of_le hb (by linarith)
  apply (hasSum_iff_tendsto_nat_of_nonneg hn _).mpr
  simp only [shifted_reciprocal_sums]
  have ha : Tendsto (fun n : ℕ=>1/(x+(n:ℝ))) atTop (𝓝 0) := by
    simpa only [one_div, Function.comp_def] using
      (tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_left atTop x tendsto_natCast_atTop_atTop))
  have ht:=((cot_sum_real h0 h1).tendsto_sum_nat.add_const (1/x)).sub ha
  simpa only [sub_add_cancel,sub_zero] using ht
noncomputable def tanTerm (m : ℝ) (n : ℕ) : ℝ :=
  1/(((n:ℝ)+1/2)*Real.pi-m)-1/(((n:ℝ)+1/2)*Real.pi+m)
lemma tanTerm_nonneg {m : ℝ} (hm : 0 ≤ m) (hM : m < Real.pi / 2) (n : ℕ) :
    0≤tanTerm m n := by
  have h : 0<((n:ℝ)+1/2)*Real.pi-m := by
    have hn : (0:ℝ)≤n := by positivity
    nlinarith [Real.pi_pos]
  exact sub_nonneg.mpr (one_div_le_one_div_of_le h (by linarith))
lemma tan_partial_fractions {m : ℝ} (hm : 0 ≤ m) (hM : m < Real.pi / 2) :
    HasSum (tanTerm m) (Real.tan m) := by
  let x : ℝ:=1/2-m/Real.pi
  have hp:=Real.pi_pos
  have hx0 : 0<x := by dsimp [x];rw [sub_pos,div_lt_iff₀ hp];linarith
  have hx1 : x≤1/2 := by dsimp [x];have hh:=div_nonneg hm hp.le;linarith
  have hx := (positive_shifted_reciprocal_hasSum hx0 hx1).div_const Real.pi
  have harg : Real.pi*x=Real.pi/2-m := by dsimp [x];field_simp
  rw [harg,Real.tan_pi_div_two_sub,inv_inv,mul_div_cancel_left₀ _ Real.pi_ne_zero] at hx
  apply hx.congr_fun
  intro n
  have he₁ : x+(n:ℝ)=(((n:ℝ)+1/2)*Real.pi-m)/Real.pi := by
    dsimp [x];field_simp; ring
  have he₂ : x-((n:ℝ)+1)=-(((n:ℝ)+1/2)*Real.pi+m)/Real.pi := by
    dsimp [x];field_simp; ring
  rw [he₁,he₂]
  simp only [one_div_div, neg_div, div_neg, sub_eq_add_neg]
  dsimp [tanTerm]
  field_simp; ring
end CriticalHoneycomb.FiniteFunctional.Analytic

end


section
namespace CriticalHoneycomb.FiniteFunctional.Analytic
open Real Filter Topology MeasureTheory
noncomputable def laplaceTerm (m : ℝ) (n : ℕ) (z : ℝ) : ℝ :=
  Real.exp (-(((n:ℝ)+1/2)*Real.pi-m)*z)-
  Real.exp (-(((n:ℝ)+1/2)*Real.pi+m)*z)
lemma laplaceTerm_nonneg {m z : ℝ} (hm : 0 ≤ m) (hz : 0 ≤ z) (n : ℕ) :
    0 ≤ laplaceTerm m n z := by
  apply sub_nonneg.mpr
  apply Real.exp_le_exp.mpr
  nlinarith
lemma laplaceTerm_integrable {m : ℝ} (hm : 0 ≤ m) (hM : m < Real.pi/2) (n : ℕ) :
    IntegrableOn (laplaceTerm m n) (Set.Ioi 0) := by
  have hn : (0:ℝ)≤n := by positivity
  exact (integrableOn_exp_mul_Ioi (by nlinarith [Real.pi_pos]) 0).sub
    (integrableOn_exp_mul_Ioi (by nlinarith [Real.pi_pos]) 0)
lemma laplaceTerm_integral {m : ℝ} (hm : 0 ≤ m) (hM : m < Real.pi/2) (n : ℕ) :
    ∫ z in Set.Ioi (0:ℝ),laplaceTerm m n z=tanTerm m n := by
  have hn : (0:ℝ)≤n := by positivity
  have h₁ : -(((n:ℝ)+1/2)*Real.pi-m)< 0 := by nlinarith [Real.pi_pos]
  have h₂ : -(((n:ℝ)+1/2)*Real.pi+m)< 0 := by nlinarith [Real.pi_pos]
  simp only [laplaceTerm]
  rw [integral_sub (integrableOn_exp_mul_Ioi h₁ 0)
    (integrableOn_exp_mul_Ioi h₂ 0),integral_exp_mul_Ioi h₁,integral_exp_mul_Ioi h₂]
  simp only [mul_zero,Real.exp_zero,neg_div_neg_eq,tanTerm]
lemma laplaceTerm_factor (m z : ℝ) (n : ℕ) :
    laplaceTerm m n z=(Real.exp (m*z)-Real.exp (-m*z))*Real.exp (-Real.pi*z/2)*
      (Real.exp (-Real.pi*z))^n := by
  rw [←Real.exp_nat_mul]
  simp only [laplaceTerm,sub_mul,←Real.exp_add]
  congr 1 <;> congr 1 <;> ring
lemma sinh_quotient_exponential (m z : ℝ) :
    Real.sinh (m*z)/Real.sinh (Real.pi*z/2)=
      ((Real.exp (m*z)-Real.exp (-m*z))*Real.exp (-Real.pi*z/2))/(1-Real.exp (-Real.pi*z)) := by
  have he : Real.exp (Real.pi*z/2)*Real.exp (-Real.pi*z/2)=1 := by
    rw [←Real.exp_add];ring_nf;simp
  have hf : Real.exp (-Real.pi*z)=Real.exp (-Real.pi*z/2)^2 := by
    rw [←Real.exp_nat_mul];congr 1;ring
  have hd : 1-Real.exp (-Real.pi*z/2)^2=
      (Real.exp (Real.pi*z/2)-Real.exp (-Real.pi*z/2))*Real.exp (-Real.pi*z/2) := by
    nlinarith [he]
  rw [Real.sinh_eq,Real.sinh_eq]
  rw [show -(m*z)=-m*z by ring,show -(Real.pi*z/2)=-Real.pi*z/2 by ring,hf,hd]
  rw [div_div_div_cancel_right₀ (by norm_num : (2:ℝ)≠0)]
  exact (mul_div_mul_right _ _ (Real.exp_ne_zero _)).symm
lemma sinh_kernel_hasSum (m : ℝ) {z : ℝ} (hz : 0 < z) :
    HasSum (fun n=>laplaceTerm m n z) (Real.sinh (m*z)/Real.sinh (Real.pi*z/2)) := by
  have hq : ‖Real.exp (-Real.pi*z)‖< 1 := by
    rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _),Real.exp_lt_one_iff]
    nlinarith [Real.pi_pos]
  have h:=(hasSum_geometric_of_norm_lt_one hq).mul_left
    ((Real.exp (m*z)-Real.exp (-m*z))*Real.exp (-Real.pi*z/2))
  rw [sinh_quotient_exponential,div_eq_mul_inv]
  exact h.congr_fun (laplaceTerm_factor m z)
lemma sinh_kernel_integral_nonneg {m : ℝ} (hm : 0 ≤ m) (hM : m < Real.pi/2) :
    ∫ z in Set.Ioi (0:ℝ),Real.sinh (m*z)/Real.sinh (Real.pi*z/2)=Real.tan m := by
  have he (n : ℕ) : ∫ z in Set.Ioi (0:ℝ),‖laplaceTerm m n z‖=tanTerm m n := by
    rw [←laplaceTerm_integral hm hM n]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro z hz
    exact Real.norm_of_nonneg (laplaceTerm_nonneg hm hz.le n)
  have hs := hasSum_integral_of_summable_integral_norm
    (fun n=>laplaceTerm_integrable hm hM n)
    (show Summable (fun n=>∫ z in Set.Ioi (0:ℝ),‖laplaceTerm m n z‖) by
      simpa only [he] using (tan_partial_fractions hm hM).summable)
  simp_rw [laplaceTerm_integral hm hM] at hs
  have hi : (∫ z in Set.Ioi (0:ℝ),∑' n,laplaceTerm m n z)=
      ∫ z in Set.Ioi (0:ℝ),Real.sinh (m*z)/Real.sinh (Real.pi*z/2) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro z hz
    exact (sinh_kernel_hasSum m hz).tsum_eq
  rw [hi] at hs
  exact hs.unique (tan_partial_fractions hm hM)
lemma sinh_kernel_integrable_nonneg {m : ℝ} (hm : 0 ≤ m) (hM : m < Real.pi/2) :
    IntegrableOn (fun z=>Real.sinh (m*z)/Real.sinh (Real.pi*z/2)) (Set.Ioi 0) := by
  rcases hm.eq_or_lt with hm|hm
  · subst m;simp
  · apply Integrable.of_integral_ne_zero
    rw [sinh_kernel_integral_nonneg hm.le hM]
    exact (Real.tan_pos_of_pos_of_lt_pi_div_two hm hM).ne'
lemma sinh_kernel_integrable {m : ℝ} (hm : |m| < Real.pi/2) :
    IntegrableOn (fun z=>Real.sinh (m*z)/Real.sinh (Real.pi*z/2)) (Set.Ioi 0) := by
  by_cases h : 0 ≤ m
  · exact sinh_kernel_integrable_nonneg h (lt_of_le_of_lt (le_abs_self _) hm)
  · have hn : 0 ≤ -m := by linarith
    have h:=(sinh_kernel_integrable_nonneg hn (by simpa [abs_of_neg (lt_of_not_ge h)] using hm)).neg
    change IntegrableOn (fun z=>-(Real.sinh (-m*z)/Real.sinh (Real.pi*z/2))) (Set.Ioi 0) at h
    simpa only [neg_mul,Real.sinh_neg,neg_div,neg_neg] using h
lemma sinh_kernel_integral {m : ℝ} (hm : |m| < Real.pi/2) :
    ∫ z in Set.Ioi (0:ℝ),Real.sinh (m*z)/Real.sinh (Real.pi*z/2)=Real.tan m := by
  by_cases h : 0 ≤ m
  · exact sinh_kernel_integral_nonneg h (lt_of_le_of_lt (le_abs_self _) hm)
  · have hn : 0 ≤ -m := by linarith
    have he:=sinh_kernel_integral_nonneg hn (by simpa [abs_of_neg (lt_of_not_ge h)] using hm)
    simp only [neg_mul,Real.sinh_neg,neg_div,integral_neg,Real.tan_neg] at he
    linarith
end CriticalHoneycomb.FiniteFunctional.Analytic

end


section
namespace CriticalHoneycomb.FiniteFunctional.Analytic
open Real Filter Topology MeasureTheory
lemma cosh_sinh_split (u m z : ℝ) :
    Real.cosh (u*z)*Real.sinh (m*z)=
      (Real.sinh ((m+u)*z)+Real.sinh ((m-u)*z))/2 := by
  rw [add_mul,sub_mul,Real.sinh_add,Real.sinh_sub]
  ring
lemma cosh_sinh_kernel_integrable {u m : ℝ} (h : |m|+|u| < Real.pi/2) :
    IntegrableOn (fun z=>Real.cosh (u*z)*Real.sinh (m*z)/Real.sinh (Real.pi*z/2)) (Set.Ioi 0) := by
  have h₁ : |m+u| < Real.pi/2 := lt_of_le_of_lt (abs_add_le _ _) h
  have h₂ : |m-u| < Real.pi/2 := lt_of_le_of_lt (abs_sub _ _) h
  have hi:=((sinh_kernel_integrable h₁).add (sinh_kernel_integrable h₂)).div_const 2
  apply hi.congr
  filter_upwards [] with z
  dsimp
  rw [cosh_sinh_split]
  ring
lemma cosh_sinh_kernel_integral_tan {u m : ℝ} (h : |m|+|u| < Real.pi/2) :
    ∫ z in Set.Ioi (0:ℝ),Real.cosh (u*z)*Real.sinh (m*z)/Real.sinh (Real.pi*z/2)=
      (Real.tan (m+u)+Real.tan (m-u))/2 := by
  have h₁ : |m+u| < Real.pi/2 := lt_of_le_of_lt (abs_add_le _ _) h
  have h₂ : |m-u| < Real.pi/2 := lt_of_le_of_lt (abs_sub _ _) h
  have he : (fun z=>Real.cosh (u*z)*Real.sinh (m*z)/Real.sinh (Real.pi*z/2))=
      fun z=>(Real.sinh ((m+u)*z)/Real.sinh (Real.pi*z/2)+
        Real.sinh ((m-u)*z)/Real.sinh (Real.pi*z/2))/2 := by
    funext z;rw [cosh_sinh_split];ring
  rw [he,integral_div,integral_add (sinh_kernel_integrable h₁) (sinh_kernel_integrable h₂),
    sinh_kernel_integral h₁,sinh_kernel_integral h₂]
lemma tan_midpoint_identity {u m : ℝ} (h : |m|+|u| < Real.pi/2) :
    (Real.tan (m+u)+Real.tan (m-u))/2=
      Real.sin (2*m)/(Real.cos (2*u)+Real.cos (2*m)) := by
  have h₁ : |m+u| < Real.pi/2 := lt_of_le_of_lt (abs_add_le _ _) h
  have h₂ : |m-u| < Real.pi/2 := lt_of_le_of_lt (abs_sub _ _) h
  have hc₁ := Real.cos_pos_of_mem_Ioo (abs_lt.mp h₁)
  have hc₂ := Real.cos_pos_of_mem_Ioo (abs_lt.mp h₂)
  have hd : Real.cos (2*u)+Real.cos (2*m)=2*Real.cos (m+u)*Real.cos (m-u) := by
    rw [Real.two_mul_cos_mul_cos]
    congr 1 <;> congr 1 <;> ring
  have hn : Real.sin (2*m)=Real.sin (m+u)*Real.cos (m-u)+Real.cos (m+u)*Real.sin (m-u) := by
    rw [←Real.sin_add]
    congr 1;ring
  rw [hd,hn,Real.tan_eq_sin_div_cos,Real.tan_eq_sin_div_cos]
  field_simp
lemma cosh_sinh_kernel_integral {u m : ℝ} (h : |m|+|u| < Real.pi/2) :
    ∫ z in Set.Ioi (0:ℝ),Real.cosh (u*z)*Real.sinh (m*z)/Real.sinh (Real.pi*z/2)=
      Real.sin (2*m)/(Real.cos (2*u)+Real.cos (2*m)) := by
  rw [cosh_sinh_kernel_integral_tan h,tan_midpoint_identity h]
end CriticalHoneycomb.FiniteFunctional.Analytic

end


section
namespace CriticalHoneycomb.FiniteFunctional.Analytic
open Real Filter Topology MeasureTheory
lemma exp_mul_sinh_le_sinh_add {a b : ℝ} (ha : 0 ≤ a) :
    Real.exp a*Real.sinh b ≤ Real.sinh (a+b) := by
  have he : Real.exp a*Real.sinh b=(Real.exp (a+b)-Real.exp (a-b))/2 := by
    rw [Real.sinh_eq,Real.exp_add,Real.exp_sub,Real.exp_neg]
    ring
  rw [he,Real.sinh_eq]
  have h:=Real.exp_le_exp.mpr (show -(a+b) ≤ a-b by linarith)
  linarith
lemma pow_mul_exp_le_sinh {a δ z : ℝ} (ha : 0 ≤ a) (hd : 0 < δ) (hz : 0 ≤ z) (k : ℕ) :
    z^(k+1)*Real.exp (a*z) ≤ ((k.factorial:ℝ)/δ^(k+1))*Real.sinh ((a+2*δ)*z) := by
  have hk : (0:ℝ) < k.factorial := by positivity
  have hp : 0 < δ^k := pow_pos hd _
  have hh := (div_le_iff₀ hk).mp (Real.pow_div_factorial_le_exp (δ*z) (mul_nonneg hd.le hz) k)
  rw [mul_pow] at hh
  have hpow : z^k ≤ (k.factorial:ℝ)/δ^k*Real.exp (δ*z) := by
    rw [div_mul_eq_mul_div,le_div_iff₀ hp]
    nlinarith
  have hlin : z ≤ Real.sinh (δ*z)/δ := by
    apply (le_div_iff₀ hd).mpr
    simpa [mul_comm] using Real.self_le_sinh_iff.mpr (mul_nonneg hd.le hz)
  calc
    z^(k+1)*Real.exp (a*z) = z^k*z*Real.exp (a*z) := by rw [pow_succ]
    _ ≤ ((k.factorial:ℝ)/δ^k*Real.exp (δ*z))*(Real.sinh (δ*z)/δ)*Real.exp (a*z) := by
      gcongr
    _ = ((k.factorial:ℝ)/δ^(k+1))*(Real.exp ((a+δ)*z)*Real.sinh (δ*z)) := by
      rw [add_mul,Real.exp_add,pow_succ]
      field_simp
    _ ≤ ((k.factorial:ℝ)/δ^(k+1))*Real.sinh ((a+2*δ)*z) := by
      gcongr
      convert exp_mul_sinh_le_sinh_add (b:=δ*z) (mul_nonneg (add_nonneg ha hd.le) hz) using 1; congr 1; ring
lemma polynomial_kernel_integrable (k : ℕ) {a : ℝ} (ha : 0 ≤ a) (hA : a < Real.pi/2) :
    IntegrableOn (fun z=>z^(k+1)*Real.exp (a*z)/Real.sinh (Real.pi*z/2)) (Set.Ioi 0) := by
  let δ : ℝ := (Real.pi/2-a)/4
  have hd : 0 < δ := by dsimp [δ];linarith
  have hs : |a+2*δ| < Real.pi/2 := by
    rw [abs_of_nonneg (by positivity)]
    dsimp [δ];linarith
  have hi := (sinh_kernel_integrable hs).const_mul ((k.factorial:ℝ)/δ^(k+1))
  apply hi.mono'
  · exact (by fun_prop : Measurable (fun z=>z^(k+1)*Real.exp (a*z)/Real.sinh (Real.pi*z/2))).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with z hz
    have hz0 : 0 ≤ z := hz.le
    have hden : 0 ≤ Real.sinh (Real.pi*z/2) := Real.sinh_nonneg_iff.mpr (by positivity)
    rw [Real.norm_of_nonneg (by positivity),←mul_div_assoc]
    exact div_le_div_of_nonneg_right (pow_mul_exp_le_sinh ha hd hz0 k) hden
end CriticalHoneycomb.FiniteFunctional.Analytic

end


section
namespace CriticalHoneycomb.FiniteFunctional.Analytic
open Real Filter Topology MeasureTheory
noncomputable def hypJet (j : ℕ) (x : ℝ) : ℝ :=
  (Real.exp x-(-1:ℝ)^j*Real.exp (-x))/2
@[simp] lemma hypJet_zero (x : ℝ) : hypJet 0 x=Real.sinh x := by simp [hypJet,Real.sinh_eq]
@[simp] lemma hypJet_one (x : ℝ) : hypJet 1 x=Real.cosh x := by simp [hypJet,Real.cosh_eq]
lemma hypJet_hasDerivAt (j : ℕ) (x : ℝ) : HasDerivAt (hypJet j) (hypJet (j+1) x) x := by
  have h:=((Real.hasDerivAt_exp x).sub (((hasDerivAt_id x).neg.exp).const_mul ((-1:ℝ)^j))).div_const 2
  convert h using 1 <;> try rfl
  dsimp [hypJet]
  rw [pow_succ]
  ring
lemma hypJet_abs_le (j : ℕ) (x : ℝ) : |hypJet j x| ≤ Real.exp |x| := by
  have h:=abs_sub (Real.exp x) ((-1:ℝ)^j*Real.exp (-x))
  have h₁:=Real.exp_le_exp.mpr (le_abs_self x)
  have h₂:=Real.exp_le_exp.mpr (neg_le_abs x)
  simp only [hypJet,abs_div,abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
  simp only [abs_mul,abs_pow,abs_neg,abs_one,one_pow,one_mul,
    abs_of_pos (Real.exp_pos _)] at h
  linarith
lemma cosh_abs_le_exp_abs (x : ℝ) : |Real.cosh x| ≤ Real.exp |x| := by
  simpa using hypJet_abs_le 1 x
noncomputable def transformJet (u : ℝ) (j : ℕ) (m z : ℝ) : ℝ :=
  Real.cosh (u*z)*z^j*hypJet j (m*z)/Real.sinh (Real.pi*z/2)
lemma transformJet_zero (u m z : ℝ) : transformJet u 0 m z=
    Real.cosh (u*z)*Real.sinh (m*z)/Real.sinh (Real.pi*z/2) := by
  simp [transformJet]
lemma transformJet_hasDerivAt (u : ℝ) (j : ℕ) (m z : ℝ) :
    HasDerivAt (fun t=>transformJet u j t z) (transformJet u (j+1) m z) m := by
  have h:=(((hypJet_hasDerivAt j (m*z)).comp m ((hasDerivAt_id m).mul_const z)).const_mul
    (Real.cosh (u*z)*z^j)).div_const (Real.sinh (Real.pi*z/2))
  convert h using 1 <;> try rfl
  dsimp [transformJet]
  rw [pow_succ]
  ring
lemma transformJet_norm_le {u m a z : ℝ} (j : ℕ) (hz : 0 ≤ z) (ha : |u|+|m| ≤ a) :
    ‖transformJet u j m z‖ ≤ z^j*Real.exp (a*z)/Real.sinh (Real.pi*z/2) := by
  have hd : 0 ≤ Real.sinh (Real.pi*z/2) := Real.sinh_nonneg_iff.mpr (by positivity)
  rw [Real.norm_eq_abs,transformJet,abs_div,abs_of_nonneg hd,abs_mul,abs_mul,abs_pow,abs_of_nonneg hz]
  apply div_le_div_of_nonneg_right _ hd
  calc
    |Real.cosh (u*z)| * z^j*|hypJet j (m*z)| ≤ Real.exp |u*z| * z^j*Real.exp |m*z| := by
      gcongr
      · exact cosh_abs_le_exp_abs _
      · exact hypJet_abs_le _ _
    _ = z^j*Real.exp ((|u|+|m|)*z) := by
      rw [abs_mul,abs_mul,abs_of_nonneg hz,add_mul,Real.exp_add]
      ring
    _ ≤ z^j*Real.exp (a*z) := by gcongr
lemma transformJet_integrable {u m : ℝ} (j : ℕ) (h : |m|+|u| < Real.pi/2) :
    IntegrableOn (transformJet u j m) (Set.Ioi 0) := by
  cases j with
  | zero => exact (cosh_sinh_kernel_integrable h).congr (ae_of_all _ (fun z=>(transformJet_zero u m z).symm))
  | succ j =>
    have hi:=polynomial_kernel_integrable j (add_nonneg (abs_nonneg u) (abs_nonneg m)) (by linarith : |u|+|m| < Real.pi/2)
    apply hi.mono'
    · exact (by unfold transformJet hypJet;fun_prop : Measurable (transformJet u (j+1) m)).aestronglyMeasurable
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with z hz
      exact transformJet_norm_le _ hz.le le_rfl
end CriticalHoneycomb.FiniteFunctional.Analytic

end

end OAI
