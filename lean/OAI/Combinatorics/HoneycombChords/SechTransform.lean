import OAI.Combinatorics.HoneycombChords.HyperbolicTransform

namespace OAI

/-! Exact hyperbolic secant integral transforms and pairings. -/

section
namespace CriticalHoneycomb.FiniteFunctional.Analytic
open Real Filter Topology MeasureTheory
lemma sech_split {z : ℝ} (hz : 0 < z) (u : ℝ) :
    Real.cosh (u*z)/Real.cosh (Real.pi*z/4)=
      2*(Real.cosh (u*z)*Real.sinh (Real.pi/4*z)/Real.sinh (Real.pi*z/2)) := by
  have hs : Real.sinh (Real.pi/4*z) ≠ 0 := (Real.sinh_pos_iff.mpr (by positivity)).ne'
  have hc : Real.cosh (Real.pi*z/4) ≠ 0 := (Real.cosh_pos _).ne'
  rw [show Real.pi*z/2=Real.pi/4*z+Real.pi/4*z by ring,Real.sinh_add]
  field_simp
  ring
lemma sech_kernel_integrable_pi4 {u : ℝ} (hu : |u| < Real.pi/4) :
    IntegrableOn (fun z => Real.cosh (u*z)/Real.cosh (Real.pi*z/4)) (Set.Ioi 0) := by
  have h : |Real.pi/4|+|u| < Real.pi/2 := by rw [abs_of_pos (by positivity)];linarith
  apply ((cosh_sinh_kernel_integrable h).const_mul 2).congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with z hz
  exact (sech_split hz u).symm
lemma sech_kernel_integral_pi4 {u : ℝ} (hu : |u| < Real.pi/4) :
    ∫ z in Set.Ioi (0:ℝ), Real.cosh (u*z)/Real.cosh (Real.pi*z/4)=2/Real.cos (2*u) := by
  have h : |Real.pi/4|+|u| < Real.pi/2 := by rw [abs_of_pos (by positivity)];linarith
  calc
    (∫ z in Set.Ioi (0:ℝ), Real.cosh (u*z)/Real.cosh (Real.pi*z/4))=
      ∫ z in Set.Ioi (0:ℝ),2*(Real.cosh (u*z)*Real.sinh (Real.pi/4*z)/Real.sinh (Real.pi*z/2)) := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with z hz
        exact sech_split hz u
    _=2/Real.cos (2*u) := by
      rw [integral_const_mul,cosh_sinh_kernel_integral h]
      rw [show 2*(Real.pi/4)=Real.pi/2 by ring,Real.sin_pi_div_two,Real.cos_pi_div_two]
      ring
lemma sech_scale_bound {c m : ℝ} (hc : 0 < c) (hm : |m| < c) :
    |m/(4*c/Real.pi)| < Real.pi/4 := by
  have hb : 0 < 4*c/Real.pi := by positivity
  rw [abs_div,abs_of_pos hb,div_lt_iff₀ hb]
  have he : Real.pi/4*(4*c/Real.pi)=c := by field_simp
  rwa [he]
lemma sech_scaled_kernel {c : ℝ} (hc : 0 < c) (m z : ℝ) :
    Real.cosh ((m/(4*c/Real.pi))*(4*c/Real.pi*z))/
      Real.cosh (Real.pi*(4*c/Real.pi*z)/4)=Real.cosh (m*z)/Real.cosh (c*z) := by
  have hc0 : c ≠ 0 := hc.ne'
  congr 2 <;> field_simp
lemma sech_kernel_integrable {c m : ℝ} (hc : 0 < c) (hm : |m| < c) :
    IntegrableOn (fun z => Real.cosh (m*z)/Real.cosh (c*z)) (Set.Ioi 0) := by
  have hi:=sech_kernel_integrable_pi4 (sech_scale_bound hc hm)
  have ht:=(integrableOn_Ioi_comp_mul_left_iff (fun z => Real.cosh ((m/(4*c/Real.pi))*z)/
    Real.cosh (Real.pi*z/4)) 0 (by positivity : 0 < 4*c/Real.pi)).2 (by simpa using hi)
  simpa only [sech_scaled_kernel hc] using ht
lemma sech_kernel_integral {c m : ℝ} (hc : 0 < c) (hm : |m| < c) :
    ∫ z in Set.Ioi (0:ℝ), Real.cosh (m*z)/Real.cosh (c*z)=
      (Real.pi/(2*c))/Real.cos (Real.pi*m/(2*c)) := by
  have ht:=integral_comp_mul_left_Ioi (fun z => Real.cosh ((m/(4*c/Real.pi))*z)/
    Real.cosh (Real.pi*z/4)) 0 (by positivity : 0 < 4*c/Real.pi)
  simp only [sech_scaled_kernel hc,mul_zero,smul_eq_mul] at ht
  rw [ht,sech_kernel_integral_pi4 (sech_scale_bound hc hm)]
  have he : 2*(m/(4*c/Real.pi))=Real.pi*m/(2*c) := by field_simp; ring
  rw [he]
  field_simp
  ring
lemma cosh_pair_split (m n z : ℝ) :
    Real.cosh (m*z)*Real.cosh (n*z)=
      (Real.cosh ((m+n)*z)+Real.cosh ((m-n)*z))/2 := by
  rw [add_mul,sub_mul,Real.cosh_add,Real.cosh_sub]
  ring
lemma sech_pair_integrable {c m n : ℝ} (hc : 0 < c) (h : |m|+|n| < c) :
    IntegrableOn (fun z => Real.cosh (m*z)*Real.cosh (n*z)/Real.cosh (c*z)) (Set.Ioi 0) := by
  have hm:=sech_kernel_integrable hc (lt_of_le_of_lt (abs_add_le m n) h)
  have hn:=sech_kernel_integrable hc (lt_of_le_of_lt (abs_sub m n) h)
  apply ((hm.add hn).div_const 2).congr
  filter_upwards with z
  simp only [Pi.add_apply]
  rw [cosh_pair_split]
  ring
lemma sech_pair_integral {c m n : ℝ} (hc : 0 < c) (h : |m|+|n| < c) :
    ∫ z in Set.Ioi (0:ℝ),Real.cosh (m*z)*Real.cosh (n*z)/Real.cosh (c*z)=
      (Real.pi/(4*c))*(1/Real.cos (Real.pi*(m+n)/(2*c))+
        1/Real.cos (Real.pi*(m-n)/(2*c))) := by
  have hm : |m+n| < c := lt_of_le_of_lt (abs_add_le m n) h
  have hn : |m-n| < c := lt_of_le_of_lt (abs_sub m n) h
  have he : (fun z => Real.cosh (m*z)*Real.cosh (n*z)/Real.cosh (c*z))=
      fun z => (Real.cosh ((m+n)*z)/Real.cosh (c*z)+Real.cosh ((m-n)*z)/Real.cosh (c*z))/2 := by
    funext z;rw [cosh_pair_split];ring
  rw [he,integral_div,integral_add (sech_kernel_integrable hc hm) (sech_kernel_integrable hc hn),
    sech_kernel_integral hc hm,sech_kernel_integral hc hn]
  ring
end CriticalHoneycomb.FiniteFunctional.Analytic

end



end OAI
