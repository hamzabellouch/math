import OAI.Analysis.PlanarPacking.Entire
import OAI.Analysis.PlanarPacking.CanonicalRows

namespace OAI

/-!
# Direct spectral estimates

The norm of the direct spectral kernel gives derivative bounds for cardinal functions.
-/

namespace SharpPlanar
open MeasureTheory Set IntegerBasis
open scoped BigOperators
lemma directKernel_norm (ell : ℕ) (s t : ℝ) :
    ‖directKernel ell s t‖=(Real.pi*|t|)^ell := by
  unfold directKernel
  rw [norm_mul,norm_pow,norm_mul,norm_mul,Complex.norm_I,Complex.norm_real,
    Real.norm_eq_abs,abs_of_pos Real.pi_pos,one_mul,Complex.norm_real,Real.norm_eq_abs,
    Complex.norm_exp]
  have he : (Complex.I*Real.pi*(t:ℂ)*s).re=0 := by simp
  rw [he,Real.exp_zero,mul_one]
lemma direct_piece_bound (p : CardinalData) (j : Fin 6) (ell : ℕ) (s : ℝ) :
    ‖∫ t in (j.val:ℝ)/6..((j.val:ℝ)+1)/6, density p j.val t*directKernel ell s t‖ ≤
      (|p.c₀|+|p.d₀|+‖p.x‖)*densityCap j/6*(Real.pi*((j.val:ℝ)+1)/6)^ell := by
  have hlen : ((j.val:ℝ)+1)/6-(j.val:ℝ)/6=1/6 := by ring
  have hlu : (j.val:ℝ)/6 ≤ ((j.val:ℝ)+1)/6 := by linarith
  have hh := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (j.val:ℝ)/6) (b := ((j.val:ℝ)+1)/6)
    (C := (|p.c₀|+|p.d₀|+‖p.x‖)*densityCap j*(Real.pi*((j.val:ℝ)+1)/6)^ell)
    (f := fun t => density p j.val t*directKernel ell s t) (fun t ht => by
      have ht' : t ∈ Set.Icc ((j.val:ℝ)/6) (((j.val:ℝ)+1)/6) :=
        uIcc_of_le hlu ▸ Set.uIoc_subset_uIcc ht
      have ht0 : 0≤t := (by positivity : (0:ℝ)≤(j.val:ℝ)/6).trans ht'.1
      rw [norm_mul,directKernel_norm,abs_of_nonneg ht0]
      have hd:=piece_density_bound p j ht'
      have hk : (Real.pi*t)^ell≤(Real.pi*((j.val:ℝ)+1)/6)^ell := by
        apply pow_le_pow_left₀ (mul_nonneg Real.pi_pos.le ht0)
        nlinarith [Real.pi_pos,ht'.2]
      have h:=mul_le_mul hd hk (by positivity : 0≤(Real.pi*t)^ell)
        (mul_nonneg (densityCap_nonneg j) (by positivity))
      simpa only [mul_comm (densityCap j) (|p.c₀|+|p.d₀|+‖p.x‖)] using h)
  rw [hlen,abs_of_nonneg (by norm_num : (0:ℝ)≤1/6)] at hh
  convert hh using 1; ring
lemma direct_positive_bound (x : X) (ell : ℕ) (s : ℝ) :
    |cardinalSeries (positiveData x) ell s| ≤
      ‖x‖*(∑ j : Fin 6,densityCap j/6*(Real.pi*((j.val:ℝ)+1)/6)^ell) := by
  have he := directDensity_series (positiveData x) ell s
  have he' : cardinalSeries (positiveData x) ell s=
      (∑ j ∈ Finset.range 6,∫ t in (j:ℝ)/6..((j:ℝ)+1)/6,
        density (positiveData x) j t*directKernel ell s t).re := by
    rw [he]
    simp only [cardinalSeries,positiveData,zero_mul,zero_add]
  rw [he']
  apply (Complex.abs_re_le_norm _).trans
  rw [← Fin.sum_univ_eq_sum_range,Finset.mul_sum]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro j _
  simpa only [positiveData,abs_zero,zero_add,mul_div_assoc,mul_assoc] using
    direct_piece_bound (positiveData x) j ell s
end SharpPlanar

end OAI
