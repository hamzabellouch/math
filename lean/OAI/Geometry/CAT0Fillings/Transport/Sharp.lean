import Mathlib
import OAI.Geometry.CAT0Fillings.Bubble.Euclidean
import OAI.Geometry.CAT0Fillings.Transport.Normalization

namespace OAI

section

open Set Filter MeasureTheory
open scoped Topology NNReal

namespace CAT0Fillings.RadialSobolev

lemma bubble_intervals_tendsto {n : ℕ} (hn : 2 < n) :
    Tendsto (fun D : ℝ => ∫ r in (0:ℝ)..D, r^(n-1)*(bubble n r)^(sobolevP n)) atTop (𝓝 (bubbleMass n)) ∧
    Tendsto (fun D : ℝ => ∫ r in (0:ℝ)..D, r^(n-1)*(bubble n r)^(sobolevQ n)) atTop (𝓝 (sobolevQ n*bubbleMass n)) ∧
    Tendsto (fun D : ℝ => ∫ r in (0:ℝ)..D, r^(n-1)*(bubble n r)^(sobolevP n)*r^2) atTop
      (𝓝 ((n:ℝ)/(n-2)*bubbleMass n)) := by
  have hi := bubble_moments_integrable hn
  have he := bubble_moments hn
  constructor
  · simpa only [id_eq,he.1] using intervalIntegral_tendsto_integral_Ioi 0 hi.1 tendsto_id
  constructor
  · simpa only [id_eq,he.2.1] using intervalIntegral_tendsto_integral_Ioi 0 hi.2.1 tendsto_id
  · simpa only [id_eq,he.2.2] using intervalIntegral_tendsto_integral_Ioi 0 hi.2.2 tendsto_id

lemma sobolev_power_complement {n : ℕ} (hn : 2 < n) : 1-2/sobolevP n = 2/(n:ℝ) := by
  have h : (0:ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hd : (n:ℝ)-2 ≠ 0 := ne_of_gt (sub_pos.mpr (by exact_mod_cast hn))
  dsimp [sobolevP]
  field_simp
  ring

lemma bubble_normalization_energy {n : ℕ} {F : ℝ} (hn : 2 < n) (hF : 0 < F) :
    bubbleMass n*(F/bubbleMass n)^(2/sobolevP n) =
      (bubbleMass n)^(2/(n:ℝ))*F^(2/sobolevP n) := by
  have hI := bubble_mass_pos hn
  rw [Real.div_rpow hF.le hI.le]
  calc
    _ = ((bubbleMass n)^(1:ℝ)/(bubbleMass n)^(2/sobolevP n))*F^(2/sobolevP n) := by rw [Real.rpow_one]; ring
    _ = _ := by rw [←Real.rpow_sub hI,sobolev_power_complement hn]

theorem radial_sharp {n : ℕ} {R : ℝ} {f : ℝ → ℝ} {K : ℝ≥0}
    (hn : 2 < n) (hR : 0 < R) (hf : LipschitzWith K f)
    (hfp : ∀ r ∈ Ioo 0 R, 0 < f r) (hfR : f R = 0) :
    (n:ℝ)*(n-2)*(bubbleMass n)^(2/(n:ℝ))*
      (∫ r in (0:ℝ)..R,r^(n-1)*(f r)^(sobolevP n))^(2/sobolevP n) ≤
      ∫ r in (0:ℝ)..R,r^(n-1)*(deriv f r)^2 := by
  let F := ∫ r in (0:ℝ)..R,r^(n-1)*(f r)^(sobolevP n)
  let E := ∫ r in (0:ℝ)..R,r^(n-1)*(deriv f r)^2
  have hs := sobolev_exponents hn
  have hF : 0 < F := radial_integral_pos (by omega) hs.1 hR hf.continuous hfp
  have hI := bubble_mass_pos hn
  have hi := bubble_intervals_tendsto hn
  have hdiv : Tendsto (fun D : ℝ => F/(∫ r in (0:ℝ)..D,r^(n-1)*(bubble n r)^(sobolevP n)))
      atTop (𝓝 (F/bubbleMass n)) := tendsto_const_nhds.div hi.1 hI.ne'
  have hp : ContinuousAt (fun x : ℝ => x^(2/sobolevP n)) (F/bubbleMass n) :=
    (Real.continuousAt_rpow_const _ _ (Or.inl (div_pos hF hI).ne'))
  have hl := ((hi.2.1.pow 2).const_mul ((n:ℝ)^2)).mul (hp.tendsto.comp hdiv)
  have hr := hi.2.2.const_mul ((sobolevQ n)^2*E)
  have ht := le_of_tendsto_of_tendsto hl hr (by
    filter_upwards [eventually_gt_atTop (0:ℝ)] with D hD
    exact normalize_transport_estimate hn hR hD hf hfp hfR)
  have hnR : (2:ℝ) < n := by exact_mod_cast hn
  have hq : 0 < sobolevQ n := lt_of_lt_of_le zero_lt_one hs.2.1
  have he : (n:ℝ)*(n-2)*bubbleMass n*(F/bubbleMass n)^(2/sobolevP n) ≤ E := by
    have hfactor : 0 < (sobolevQ n)^2*(n:ℝ)/(n-2)*bubbleMass n := by positivity
    apply (mul_le_mul_iff_right₀ hfactor).mp
    convert ht using 1 <;> dsimp [F,E] <;> field_simp [ne_of_gt (sub_pos.mpr hnR)]
  rw [mul_assoc ((n:ℝ)*(n-2)),bubble_normalization_energy hn hF] at he
  simpa only [mul_assoc] using he

end CAT0Fillings.RadialSobolev
end

section

open Set Filter MeasureTheory
open scoped Topology NNReal

namespace CAT0Fillings.RadialSobolev

lemma omega_pos {n : ℕ} (hn : 0 < n) : 0 < omega n := by
  rw [omega_gamma hn]
  have h : (0:ℝ) < n := by exact_mod_cast hn
  exact div_pos (pow_pos (Real.sqrt_pos.mpr Real.pi_pos) _) (Real.Gamma_pos_of_pos (by positivity))

lemma sphere_rpow_bubble {n : ℕ} (hn : 2 < n) :
    (sphereArea n)^(2/(n:ℝ)) =
      4*((n:ℝ)*omega n*bubbleMass n)^(2/(n:ℝ)) := by
  have hn0 : (0:ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hω := omega_pos (show 0 < n by omega)
  rw [←bubble_mass_sphere hn, Real.mul_rpow (by positivity)
    (mul_nonneg (mul_nonneg hn0.le hω.le) (bubble_mass_pos hn).le)]
  have he : ((2:ℝ)^n)^(2/(n:ℝ)) = 4 := by
    rw [←Real.rpow_natCast, ←Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
    have hx : (n:ℝ)*(2/(n:ℝ)) = 2 := by field_simp
    rw [hx,Real.rpow_two]
    norm_num
  rw [he]

lemma polar_sharp_coefficient {n : ℕ} {F E : ℝ} (hn : 2 < n) (hF : 0 ≤ F)
    (hE : (n:ℝ)*(n-2)*(bubbleMass n)^(2/(n:ℝ))*F^(2/sobolevP n) ≤ E) :
    (n:ℝ)*(sphereArea n)^(2/(n:ℝ))*((n:ℝ)*omega n*F)^(2/sobolevP n) ≤
      4/(n-2)*((n:ℝ)*omega n*E) := by
  have hn0 : (0:ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hn2 : (0:ℝ) < (n:ℝ)-2 := sub_pos.mpr (by exact_mod_cast hn)
  have hω := omega_pos (show 0 < n by omega)
  have hc : 0 < (n:ℝ)*omega n := mul_pos hn0 hω
  have he : 2/(n:ℝ)+2/sobolevP n = 1 := by linarith [sobolev_power_complement hn]
  have hp : ((n:ℝ)*omega n)^(2/(n:ℝ))*((n:ℝ)*omega n)^(2/sobolevP n) = (n:ℝ)*omega n := by
    rw [←Real.rpow_add hc,he,Real.rpow_one]
  have hh := mul_le_mul_of_nonneg_left hE (show 0 ≤ 4*((n:ℝ)*omega n)/(n-2) by positivity)
  rw [sphere_rpow_bubble hn,Real.mul_rpow hc.le (bubble_mass_pos hn).le,
    Real.mul_rpow hc.le hF]
  have hh' : 4*(n:ℝ)*((n:ℝ)*omega n)*(bubbleMass n)^(2/(n:ℝ))*F^(2/sobolevP n) ≤
      4/(n-2)*((n:ℝ)*omega n*E) := by
    convert hh using 1 <;> first | rfl | field_simp [hn2.ne']
  calc
    _ = 4*(n:ℝ)*
        (((n:ℝ)*omega n)^(2/(n:ℝ))*((n:ℝ)*omega n)^(2/sobolevP n))*
        (bubbleMass n)^(2/(n:ℝ))*F^(2/sobolevP n) := by ring
    _ ≤ _ := by rw [hp]; exact hh'

theorem radial_sharp_polar {n : ℕ} {R : ℝ} {f : ℝ → ℝ} {K : ℝ≥0}
    (hn : 2 < n) (hR : 0 < R) (hf : LipschitzWith K f)
    (hfp : ∀ r ∈ Ioo 0 R, 0 < f r) (hfR : f R = 0) :
    (n:ℝ)*(sphereArea n)^(2/(n:ℝ))*
      ((n:ℝ)*omega n*(∫ r in (0:ℝ)..R,r^(n-1)*(f r)^(sobolevP n)))^(2/sobolevP n) ≤
      4/(n-2)*((n:ℝ)*omega n*(∫ r in (0:ℝ)..R,r^(n-1)*(deriv f r)^2)) := by
  exact polar_sharp_coefficient hn
    (radial_integral_pos (by omega) (sobolev_exponents hn).1 hR hf.continuous hfp).le
    (radial_sharp hn hR hf hfp hfR)

end CAT0Fillings.RadialSobolev
end

end OAI
