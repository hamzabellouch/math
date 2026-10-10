import Mathlib
import OAI.Probability.GaussianInformation.Kernel.MixedProjection

namespace OAI
open MeasureTheory ProbabilityTheory Metric Set
open scoped ENNReal
namespace KernelPotential
open Filter
open scoped Topology NNReal
namespace Reweight
open Coercivity Sphere
noncomputable def rho {d : ℕ} (ν : Measure (Ambient d)) : Measure (Ambient d) :=
  ν.withDensity (fun s => (J ν s)⁻¹)

lemma rho_ac {d : ℕ} (ν : Measure (Ambient d)) : rho ν ≪ ν :=
  withDensity_absolutelyContinuous _ _

lemma local_lower_J {d : ℕ} (ν : Measure (Ambient d)) (z : Ambient d) {r : ℝ}
    (hr : 0 < r) (s : Ambient d) (hs : s ∈ ball z r) :
    ν (ball z r) / ENNReal.ofReal ((2*r)^(2*(d/16))) ≤ J ν s := by
  rw [div_eq_mul_inv]
  calc
    _ = ∫⁻ u in ball z r, (ENNReal.ofReal ((2*r)^(2*(d/16))))⁻¹ ∂ν := by simp [mul_comm]
    _ ≤ ∫⁻ u in ball z r,(ENNReal.ofReal ‖u-s‖)⁻¹^(2*(d/16)) ∂ν := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem measurableSet_ball] with u hu
      rw [ENNReal.ofReal_pow (by positivity),ENNReal.inv_pow]
      have hdist : ‖u-s‖ ≤ 2*r := by
        rw [← dist_eq_norm]
        exact le_of_lt (calc dist u s ≤ dist u z+dist z s := dist_triangle _ _ _
          _ < r+r := add_lt_add hu (by simpa [dist_comm] using hs)
          _ = 2*r := by ring)
      exact pow_le_pow_left₀ zero_le (ENNReal.inv_le_inv.mpr (ENNReal.ofReal_le_ofReal hdist)) _
    _ ≤ J ν s := lintegral_mono' Measure.restrict_le_self (le_refl _)

lemma rho_ball {d : ℕ} (ν : Measure (Ambient d)) [IsProbabilityMeasure ν]
    (z : Ambient d) {r : ℝ} (hr : 0 < r) :
    rho ν (ball z r) ≤ ENNReal.ofReal ((2*r)^(2*(d/16))) := by
  by_cases hm : ν (ball z r) = 0
  · have hz := rho_ac ν hm
    rw [hz]; exact bot_le
  have hmt : ν (ball z r) ≠ ∞ := measure_ne_top _ _
  unfold rho
  rw [withDensity_apply _ measurableSet_ball]
  calc
    _ ≤ ∫⁻ s in ball z r, ENNReal.ofReal ((2*r)^(2*(d/16))) / ν (ball z r) ∂ν := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem measurableSet_ball] with s hs
      have h := ENNReal.inv_le_inv.mpr (local_lower_J ν z hr s hs)
      simpa only [ENNReal.inv_div (Or.inl ENNReal.ofReal_ne_top) (Or.inr hm)] using h
    _ = _ := by
      simp only [lintegral_const,Measure.restrict_apply_univ]
      rw [ENNReal.div_mul_cancel hm hmt]

lemma rho_le {d : ℕ} (ν : Measure (Ambient d)) [IsProbabilityMeasure ν]
    (hν : ∀ᵐ s ∂ν, ‖s‖=1) : rho ν ≤ ENNReal.ofReal ((2:ℝ)^(2*(d/16))) • ν := by
  intro E
  unfold rho
  rw [withDensity_apply' _ E,Measure.smul_apply,smul_eq_mul]
  calc
    _ ≤ ∫⁻ s in E, ENNReal.ofReal ((2:ℝ)^(2*(d/16))) ∂ν := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_of_ae hν] with s hs
      have h := ENNReal.inv_le_inv.mpr (lower_J_on_sphere ν hν s hs)
      simpa only [ENNReal.ofReal_pow (by norm_num : (0:ℝ) ≤ 1/2),ENNReal.inv_pow,
        show (ENNReal.ofReal (1/2:ℝ))⁻¹ = ENNReal.ofReal (2:ℝ) by rw [← ENNReal.ofReal_inv_of_pos (by norm_num)]; norm_num,
        ENNReal.ofReal_pow (by norm_num : (0:ℝ) ≤ 2)] using h
    _ = _ := by simp

lemma rho_bounded {d : ℕ} (hd : 0 < d) (ν : Measure (Ambient d))
    [IsProbabilityMeasure ν] {H : ℝ} (hH : 0 < H)
    (hν : ν ≤ ENNReal.ofReal H • sphereProbability d) :
    rho ν ≤ ENNReal.ofReal ((2:ℝ)^(2*(d/16))*H) • sphereProbability d := by
  have hac : ν ≪ sphereProbability d := Measure.absolutelyContinuous_of_le_smul hν
  have hsupport : ∀ᵐ s ∂ν, ‖s‖=1 := hac.ae_le (ae_unit_norm hd)
  calc
    rho ν ≤ ENNReal.ofReal ((2:ℝ)^(2*(d/16))) • ν := rho_le ν hsupport
    _ ≤ ENNReal.ofReal ((2:ℝ)^(2*(d/16))) • (ENNReal.ofReal H • sphereProbability d) := by
      intro E
      simp only [Measure.smul_apply,smul_eq_mul]
      gcongr; exact hν E
    _ = _ := by rw [smul_smul,← ENNReal.ofReal_mul' hH.le]

lemma rho_finite {d : ℕ} (ν : Measure (Ambient d)) [IsProbabilityMeasure ν]
    (hν : ∀ᵐ s ∂ν, ‖s‖=1) : IsFiniteMeasure (rho ν) := by
  have := Measure.smul_finite ν (c := ENNReal.ofReal ((2:ℝ)^(2*(d/16)))) ENNReal.ofReal_ne_top
  exact isFiniteMeasure_of_le _ (rho_le ν hν)

lemma rho_two_ball_bounds {d : ℕ} (hd : 16 ≤ d) (ν : Measure (Ambient d))
    [IsProbabilityMeasure ν] {H : ℝ} (hH : 0 < H)
    (hν : ν ≤ ENNReal.ofReal H • sphereProbability d) (z : Ambient d) {r : ℝ} (hr : 0 < r) :
    rho ν (ball z r) ≤ ENNReal.ofReal ((2:ℝ)^(2*(d/16))*r^(2*(d/16))) ∧
    rho ν (ball z r) ≤ ENNReal.ofReal ((2:ℝ)^(2*(d/16))*H*(9*3^d)*r^(d-1)) := by
  refine ⟨by simpa only [mul_pow] using rho_ball ν z hr,?_⟩
  calc
    _ ≤ (ENNReal.ofReal ((2:ℝ)^(2*(d/16))*H) • sphereProbability d) (ball z r) := rho_bounded (by omega) ν hH hν _
    _ = ENNReal.ofReal ((2:ℝ)^(2*(d/16))*H) * sphereProbability d (ball z r) := by rw [Measure.smul_apply,smul_eq_mul]
    _ ≤ ENNReal.ofReal ((2:ℝ)^(2*(d/16))*H) * ENNReal.ofReal ((9*3^d:ℝ)*r^(d-1)) := by gcongr; exact cap_bound (by omega) z hr
    _ = _ := by rw [← ENNReal.ofReal_mul (by positivity)]; congr 1; ring

noncomputable def centeredRho {d : ℕ} (ν : Measure (Ambient d)) (s : Ambient d) : Measure (Ambient d) :=
  (rho ν).map (fun u => u-s)

lemma centered_ball {d : ℕ} (ν : Measure (Ambient d)) (s z : Ambient d) (r : ℝ) :
    centeredRho ν s (ball z r)=rho ν (ball (z+s) r) := by
  rw [centeredRho,Measure.map_apply (f := fun u : Ambient d => u-s) (measurable_id.sub measurable_const) measurableSet_ball]
  congr 1
  ext u
  simp only [mem_preimage,mem_ball,dist_eq_norm]
  abel_nf

lemma centered_finite {d : ℕ} (ν : Measure (Ambient d)) [IsProbabilityMeasure ν]
    (hν : ∀ᵐ s ∂ν, ‖s‖=1) (s : Ambient d) : IsFiniteMeasure (centeredRho ν s) := by
  have := rho_finite ν hν
  unfold centeredRho
  infer_instance

lemma centered_support {d : ℕ} (ν : Measure (Ambient d)) [IsProbabilityMeasure ν]
    (hν : ∀ᵐ s ∂ν, ‖s‖=1) (s : Ambient d) (hs : ‖s‖=1) :
    ∀ᵐ u ∂centeredRho ν s, ‖u‖ ≤ 2 := by
  apply (ae_map_iff (measurable_id.sub measurable_const).aemeasurable
    (measurableSet_le measurable_norm measurable_const)).mpr
  filter_upwards [(rho_ac ν).ae_le hν] with u hu
  calc ‖u-s‖ ≤ ‖u‖+‖s‖ := norm_sub_le _ _
    _ = 2 := by rw [hu,hs]; norm_num

lemma centered_mixed_moment {d : ℕ} (hd : 16 ≤ d) (ν : Measure (Ambient d))
    [IsProbabilityMeasure ν] {H : ℝ} (hH : 0 < H)
    (hν : ν ≤ ENNReal.ofReal H • sphereProbability d) (s : Ambient d) (hs : ‖s‖=1)
    (L : ℕ) (hL : H*(9*3^d:ℝ) ≤ 2^L) (η : ℝ) (hη : 0 < η) :
    (∫⁻ X, (∫⁻ Z, Projection.mixedCubeAverage (centeredRho ν s) η X Z
      ∂Projection.Support.gaussianRows (d/16) d)^(d/16)
      ∂Projection.Support.gaussianRows (d/16) d) ≤
      ENNReal.ofReal ((9^(d/16-1)*3^(d-1)*2^((d-1)+4*(d/16)+2):ℝ)*((L:ℝ)+2))^(d/16) := by
  have hac : ν ≪ sphereProbability d := Measure.absolutelyContinuous_of_le_smul hν
  have hsupport := hac.ae_le (ae_unit_norm (by omega : 0 < d))
  have := centered_finite ν hsupport s
  have hB (z : Ambient d) (r : ℝ) (hr : 0 < r) :
      centeredRho ν s (ball z r) ≤ ENNReal.ofReal ((2:ℝ)^(2*(d/16))*r^(2*(d/16))) := by
    rw [centered_ball]
    exact (rho_two_ball_bounds hd ν hH hν (z+s) hr).1
  have hD (z : Ambient d) (r : ℝ) (hr : 0 < r) :
      centeredRho ν s (ball z r) ≤ ENNReal.ofReal ((2:ℝ)^(2*(d/16))*H*(9*3^d)*r^(d-1)) := by
    rw [centered_ball]
    exact (rho_two_ball_bounds hd ν hH hν (z+s) hr).2
  have hDB : (2:ℝ)^(2*(d/16))*H*(9*3^d) ≤ 2^(2*(d/16))*2^L := by
    nlinarith [mul_le_mul_of_nonneg_left hL (by positivity : (0:ℝ) ≤ 2^(2*(d/16)))]
  have h := Projection.mixed_fixed_origin_moment (centeredRho ν s) (B := (2:ℝ)^(2*(d/16)))
    (D := (2:ℝ)^(2*(d/16))*H*(9*3^d)) (by positivity) (by positivity)
    (by omega : 0 < d/16) (by omega : 2*(d/16) < d-1)
    (centered_support ν hsupport s hs) hB hD L hDB η hη
  convert h using 3
  congr 1
  have he : (d-1)+4*(d/16)+2=((d-1)+2*(d/16)+2)+2*(d/16) := by omega
  rw [he,pow_add]
  ring

end Reweight
end KernelPotential

end OAI
