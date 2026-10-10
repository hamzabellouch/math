import Mathlib
import OAI.Geometry.CAT0Fillings.Rearrangement.Energy
import OAI.Geometry.CAT0Fillings.Rearrangement.Euclidean

namespace OAI

section

open Set Filter MeasureTheory Metric
open scoped ENNReal NNReal Topology

namespace CAT0Fillings.Rearrangement

lemma weighted_deriv_sq_integrable {f w : ℝ → ℝ} {K : ℝ≥0} {a b : ℝ}
    (hf : LipschitzWith K f) (hw : Continuous w) (hw0 : ∀ r ∈ Icc a b, 0 ≤ w r) :
    IntegrableOn (fun r => w r*(deriv f r)^2) (Icc a b) := by
  have h := RadialSobolev.continuous_mul_deriv_memLp_Icc hw.sqrt hf a b 2
  have hi := h.integrable_mul h
  apply hi.congr
  filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
  dsimp only [Pi.mul_apply]
  calc
    _ = (Real.sqrt (w r))^2*(deriv f r)^2 := by ring
    _ = _ := by rw [Real.sq_sqrt (hw0 r hr)]

lemma inverse_profile_energy_real {R : ℝ → ℝ} {U C : ℝ} {n : ℕ} {K : ℝ≥0}
    (hR0 : 0 ≤ R 0) (hC : 0 ≤ C) (hf : LipschitzWith K (radialInverse R U)) :
    ENNReal.ofReal (C*(∫ r in (0:ℝ)..R 0,r^(n-1)*(deriv (radialInverse R U) r)^2)) =
      ∫⁻ r in Icc 0 (R 0), ENNReal.ofReal (C*r^(n-1))*
        (ENNReal.ofReal (-deriv (radialInverse R U) r))^2 := by
  have hi := weighted_deriv_sq_integrable hf (show Continuous (fun r : ℝ => r^(n-1)) by fun_prop)
    (fun r (hr : r ∈ Icc 0 (R 0)) => pow_nonneg hr.1 _)
  rw [intervalIntegral.integral_of_le hR0,←integral_Icc_eq_integral_Ioc,←integral_const_mul]
  rw [ofReal_integral_eq_lintegral_ofReal (hi.const_mul C) (by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
    exact mul_nonneg hC (mul_nonneg (pow_nonneg hr.1 _) (sq_nonneg _)))]
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
  have hd : 0 ≤ -deriv (radialInverse R U) r := neg_nonneg.mpr (radialInverse_antitone R U).deriv_nonpos
  rw [←ENNReal.ofReal_pow hd,←ENNReal.ofReal_mul (mul_nonneg hC (pow_nonneg hr.1 _))]
  congr 1
  ring

lemma radial_moment_finite_interval {f : ℝ → ℝ} {R q : ℝ} {n : ℕ}
    (hR : 0 ≤ R) (hq : 0 < q) (hf : Continuous f) (hf0 : ∀ r, 0 ≤ f r)
    (hz : ∀ r, R ≤ r → f r = 0) :
    ∫⁻ r in Ioi (0:ℝ), ENNReal.ofReal (r^(n-1))*ENNReal.ofReal ((f r)^q) =
      ENNReal.ofReal (∫ r in (0:ℝ)..R,r^(n-1)*(f r)^q) := by
  have hc : Continuous (fun r => r^(n-1)*(f r)^q) :=
    (continuous_id.pow _).mul (hf.rpow_const (fun _ => Or.inr hq.le))
  have he : ∫⁻ r in Ioi R, ENNReal.ofReal (r^(n-1))*ENNReal.ofReal ((f r)^q) = 0 := by
    apply (lintegral_congr_ae _).trans lintegral_zero
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    simp [hz r hr.le,Real.zero_rpow hq.ne']
  rw [←Ioc_union_Ioi_eq_Ioi hR,lintegral_union measurableSet_Ioi
    (disjoint_left.mpr (fun r hr ht => (not_le_of_gt ht) hr.2)),he,add_zero,
    restrict_Ioc_eq_restrict_Icc]
  rw [intervalIntegral.integral_of_le hR,←integral_Icc_eq_integral_Ioc,
    ofReal_integral_eq_lintegral_ofReal hc.integrableOn_Icc (by
      filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
      exact mul_nonneg (pow_nonneg hr.1 _) (Real.rpow_nonneg (hf0 r) _))]
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
  exact (ENNReal.ofReal_mul (pow_nonneg hr.1 _)).symm

lemma euclidean_radial_moment {n : ℕ} (hn : 0 < n) {f : ℝ → ℝ} {R q : ℝ}
    (hR : 0 ≤ R) (hq : 0 < q) (hf : Continuous f) (hf0 : ∀ r, 0 ≤ f r)
    (hz : ∀ r, R ≤ r → f r = 0) :
    ∫⁻ x : EuclideanSpace ℝ (Fin n), ENNReal.ofReal ((f ‖x‖)^q) =
      ENNReal.ofReal ((n:ℝ)*omega n*(∫ r in (0:ℝ)..R,r^(n-1)*(f r)^q)) := by
  let : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
  have hp := lintegral_fun_norm_addHaar (volume : Measure (EuclideanSpace ℝ (Fin n)))
    (fun r => ENNReal.ofReal ((f r)^q))
    ((hf.rpow_const (fun _ => Or.inr hq.le)).measurable.ennreal_ofReal)
  simp only [finrank_euclideanSpace_fin] at hp
  rw [hp,radial_moment_finite_interval hR hq hf hf0 hz]
  unfold omega
  rw [ENNReal.ofReal_mul (mul_nonneg (Nat.cast_nonneg _) ENNReal.toReal_nonneg),
    ENNReal.ofReal_mul (Nat.cast_nonneg _),ENNReal.ofReal_natCast]
  congr 2
  exact (ofReal_measureReal (measure_ball_lt_top.ne)).symm

end CAT0Fillings.Rearrangement
end

section

open Set Filter MeasureTheory Metric
open scoped ENNReal NNReal Topology

namespace CAT0Fillings.Rearrangement
open RadialSobolev

theorem rearranged_sobolev (μ ζ : Measure ℝ) [IsFiniteMeasure μ] [IsFiniteMeasure ζ]
    {n : ℕ} (hn : 2 < n) {U K η : ℝ} (hU : 0 < U) (hK : 0 < K) (hη : η < 1)
    (hpos : ∀ t ∈ Ico 0 U, 0 < μ.real (Ioi t))
    (hupper : μ (Ioi U) = 0) (hnegative : ∀ᵐ t ∂μ, 0 ≤ t) {P : ℝ → ℝ}
    (hco : ∀ᵐ t ∂volume.restrict (Ioo 0 U),
      (1-η)*((n:ℝ)*omega n*(radiusDistribution μ (omega n) n t)^(n-1)) ≤ P t ∧
      P t ≤ K*(μ.rnDeriv volume t).toReal ∧
      P t^2 ≤ (μ.rnDeriv volume t).toReal*(ζ.rnDeriv volume t).toReal) :
    (n:ℝ)*(sphereArea n)^(2/(n:ℝ)) *
      ((∫⁻ t, ENNReal.ofReal (t^(sobolevP n)) ∂μ).toReal)^(2/sobolevP n) ≤
      4/(n-2)*((1-η)⁻¹)^2*ζ.real univ := by
  have hn0 : 0 < n := by omega
  let : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn0
  have hω := omega_pos hn0
  let R := radiusDistribution μ (omega n) n
  let f := radialInverse R U
  have hc : 0 < (1-η)/K := div_pos (sub_pos.mpr hη) hK
  have hD := radius_secant_from_coarea μ hω hn0 hK
    (fun t ht => hpos t ⟨ht.1.le,ht.2⟩) (hco.mono fun _ h => ⟨h.1,h.2.1⟩)
  have hR := (radius_antitone μ (n := n) hω.le).antitoneOn (Icc 0 U)
  have hf := radialInverse_lipschitz hU.le hc hR hD
  have hR0 : 0 < R 0 := radius_pos μ hω (hpos 0 ⟨le_rfl,hU⟩)
  have hfpos : ∀ r ∈ Ioo 0 (R 0), 0 < f r := by
    intro r hr
    exact (radialInverse_superlevel hR le_rfl hU
      (radius_right_continuous μ hω hn0 0)).mpr hr.2
  have hfzero : ∀ r, R 0 ≤ r → f r = 0 := fun r hr => radialInverse_zero_outside hU.le hR hr
  have hsharp := radial_sharp_polar hn hR0 hf hfpos (hfzero _ le_rfl)
  have hmoment := rearrangement_moments (volume : Measure (EuclideanSpace ℝ (Fin n))) μ hU.le hc
    hupper hnegative (by simpa only [finrank_euclideanSpace_fin, omega, measureReal_def] using hD)
    (sobolev_exponents hn).1
  simp only [euclideanRearrangement, finrank_euclideanSpace_fin] at hmoment
  change ∫⁻ x : EuclideanSpace ℝ (Fin n), ENNReal.ofReal ((f ‖x‖)^(sobolevP n)) = _ at hmoment
  rw [euclidean_radial_moment hn0 hR0.le (sobolev_exponents hn).1 hf.continuous
    (radialInverse_nonneg R U) hfzero] at hmoment
  have hF := (radial_integral_pos hn0 (sobolev_exponents hn).1 hR0 hf.continuous hfpos).le
  have hmomentR := congrArg ENNReal.toReal hmoment
  rw [ENNReal.toReal_ofReal (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hω.le) hF)] at hmomentR
  rw [←hmomentR]
  have henergy := rearranged_profile_energy_bound μ ζ hω hn0 hU hK hη hpos hco
  dsimp only at henergy
  rw [←inverse_profile_energy_real (n := n) (C := (n:ℝ)*omega n) hR0.le
    (mul_nonneg (Nat.cast_nonneg n) hω.le) hf] at henergy
  have hEnonneg : 0 ≤ (n:ℝ)*omega n*(∫ r in (0:ℝ)..R 0,r^(n-1)*(deriv f r)^2) := by
    apply mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hω.le)
    apply intervalIntegral.integral_nonneg hR0.le
    intro r hr
    exact mul_nonneg (pow_nonneg hr.1 _) (sq_nonneg _)
  have henergyR := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top ζ univ)) henergy
  rw [ENNReal.toReal_ofReal hEnonneg,ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (sq_nonneg _)] at henergyR
  calc
    _ ≤ 4/(n-2)*((n:ℝ)*omega n*(∫ r in (0:ℝ)..R 0,r^(n-1)*(deriv f r)^2)) := hsharp
    _ ≤ _ := by
      simp only [measureReal_def]
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left henergyR (show 0 ≤ 4/((n:ℝ)-2) by
        have : (2:ℝ) < n := by exact_mod_cast hn
        positivity)

end CAT0Fillings.Rearrangement
end

end OAI
