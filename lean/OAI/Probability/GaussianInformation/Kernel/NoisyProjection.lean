import Mathlib
import OAI.Probability.GaussianInformation.Kernel.Compensation

namespace OAI
open MeasureTheory ProbabilityTheory Metric Set
open scoped ENNReal
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace KernelPotential.Noise
open MeasureTheory ProbabilityTheory Metric Set
open scoped ENNReal
open Projection.Support Projection Reweight EntropySupport DriftTools Sphere

lemma mixedCube_integrand_measurable {k d : ℕ} (η : ℝ) :
    Measurable (fun t : ((Fin k → Fin d → ℝ) × (Fin k → Fin d → ℝ)) × Ambient d =>
      boxKernel η (projectVector t.1.1 t.2) 0 * boxKernel η (projectVector t.1.2 t.2) 0) := by
  have hA := measurable_boxKernel (k := k) η
  have hP := continuous_projectVector (k := k) (d := d)
  fun_prop

lemma mixedCube_measurable {k d : ℕ} (μ : Measure (Ambient d)) [SFinite μ]
    (η : ℝ) : Measurable (fun t : (Fin k → Fin d → ℝ) × (Fin k → Fin d → ℝ) =>
      mixedCubeAverage μ η t.1 t.2) :=
  Measurable.lintegral_prod_right (mixedCube_integrand_measurable η)

lemma mixedCube_le {k d : ℕ} (μ : Measure (Ambient d)) (η : ℝ)
    (X Z : Fin k → Fin d → ℝ) :
    mixedCubeAverage μ η X Z ≤ boxScale k η^2*μ univ := by
  calc
    _ ≤ ∫⁻ _u,boxScale k η*boxScale k η ∂μ := lintegral_mono
      (fun _ => mul_le_mul' (boxKernel_le η _ _) (boxKernel_le η _ _))
    _ = _ := by simp [pow_two]

lemma centered_rho_mass {d : ℕ} (ν : Measure (Ambient d)) [IsProbabilityMeasure ν]
    (hν : ∀ᵐ s ∂ν, ‖s‖=1) (s : Ambient d) :
    centeredRho ν s univ ≤ ENNReal.ofReal ((2:ℝ)^(2*(d/16))) := by
  rw [centeredRho,Measure.map_apply (by fun_prop) MeasurableSet.univ]
  simp only [preimage_univ]
  exact (rho_le ν hν univ).trans_eq (by simp)

noncomputable def momentConstant (d L : ℕ) : ℝ :=
  (9^(d/16-1)*3^(d-1)*2^((d-1)+4*(d/16)+2):ℝ)*((L:ℝ)+2)

lemma momentConstant_pos (d L : ℕ) : 0 < momentConstant d L := by
  unfold momentConstant; positivity

lemma log_momentConstant (d L : ℕ) (hd : 16 ≤ d) :
    Real.log (4*(1+2^(2*(d/16))*momentConstant d L)) ≤
      10*(d:ℝ)+Real.log ((L:ℝ)+2) := by
  have hg : 1 ≤ momentConstant d L := by
    unfold momentConstant
    have h9 : (1:ℝ) ≤ 9^(d/16-1) := one_le_pow₀ (by norm_num)
    have h3 : (1:ℝ) ≤ 3^(d-1) := one_le_pow₀ (by norm_num)
    have h2 : (1:ℝ) ≤ 2^((d-1)+4*(d/16)+2) := one_le_pow₀ (by norm_num)
    have hL : (1:ℝ) ≤ (L:ℝ)+2 := by have := Nat.cast_nonneg (α := ℝ) L; linarith
    exact one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le h9 h3) h2) hL
  have hc : (1:ℝ) ≤ 2^(2*(d/16)) := one_le_pow₀ (by norm_num)
  have hbig : 4*(1+2^(2*(d/16))*momentConstant d L) ≤
      8*2^(2*(d/16))*momentConstant d L := by nlinarith [one_le_mul_of_one_le_of_one_le hc hg]
  have hlog := Real.log_le_log (by have := momentConstant_pos d L; positivity) hbig
  have he : Real.log (8*2^(2*(d/16))*momentConstant d L) =
      Real.log 8+(2*(d/16):ℕ)*Real.log 2+(d/16-1:ℕ)*Real.log 9+
        (d-1:ℕ)*Real.log 3+((d-1)+4*(d/16)+2:ℕ)*Real.log 2+
        Real.log ((L:ℝ)+2) := by
    rw [momentConstant]
    repeat' rw [Real.log_mul (by positivity) (by positivity)]
    simp only [Real.log_pow]
    ring
  rw [he] at hlog
  have hl8 : Real.log 8 ≤ 7 := by linarith [Real.log_le_sub_one_of_pos (show (0:ℝ)<8 by norm_num)]
  have hl9 : Real.log 9 ≤ 8 := by linarith [Real.log_le_sub_one_of_pos (show (0:ℝ)<9 by norm_num)]
  have hl3 : Real.log 3 ≤ 2 := by linarith [Real.log_le_sub_one_of_pos (show (0:ℝ)<3 by norm_num)]
  have hl2 : Real.log 2 ≤ 1 := by linarith [Real.log_le_sub_one_of_pos (show (0:ℝ)<2 by norm_num)]
  have hk : (d/16:ℕ) ≤ (d:ℝ)/16 := by
    have hh : (16*((d/16:ℕ):ℝ)) ≤ (d:ℝ) := by exact_mod_cast Nat.mul_div_le d 16
    linarith
  have hk1 : ((d/16-1:ℕ):ℝ) ≤ (d/16:ℕ) := by exact_mod_cast Nat.sub_le (d/16) 1
  have hd1 : ((d-1:ℕ):ℝ) ≤ (d:ℝ) := by exact_mod_cast Nat.sub_le d 1
  have hdR : (16:ℝ) ≤ d := by exact_mod_cast hd
  push_cast at hlog
  nlinarith [mul_le_mul_of_nonneg_left hl9 (show (0:ℝ) ≤ (d/16-1:ℕ) by positivity),
    mul_le_mul_of_nonneg_left hl3 (show (0:ℝ) ≤ (d-1:ℕ) by positivity),
    mul_le_mul_of_nonneg_left hl2 (show (0:ℝ) ≤ 2*(d/16:ℕ) by positivity),
    mul_le_mul_of_nonneg_left hl2 (show (0:ℝ) ≤ (d-1:ℕ)+4*(d/16:ℕ)+2 by positivity)]

lemma weighted_centered_projection {d : ℕ} (hd : 16 ≤ d)
    (ν : Measure (Ambient d)) [IsProbabilityMeasure ν] {H : ℝ} (hH : 0 < H)
    (hν : ν ≤ ENNReal.ofReal H • sphereProbability d) (s : Ambient d) (hs : ‖s‖=1)
    (L : ℕ) (hL : H*(9*3^d:ℝ) ≤ 2^L) {η : ℝ} (hη : 0 < η)
    (u : (Fin (d/16) → Fin d → ℝ) → ℝ) (hu : Measurable u)
    (hu0 : ∀ X,0 ≤ u X) (hu1 : ∀ X,u X ≤ 1) :
    (∫ X,u X*(∫ Z,Real.log (1+2^(2*(d/16))*
      (mixedCubeAverage (centeredRho ν s) η X Z).toReal) ∂gaussianRows (d/16) d)
      ∂gaussianRows (d/16) d) ≤
      -(∫ X,u X ∂gaussianRows (d/16) d)*Real.log (∫ X,u X ∂gaussianRows (d/16) d)/(d/16:ℕ)+
        (∫ X,u X ∂gaussianRows (d/16) d)*(10*(d:ℝ)+Real.log ((L:ℝ)+2)) := by
  have hnorm := (Measure.absolutelyContinuous_of_le_smul hν).ae_le (ae_unit_norm (by omega : 0 < d))
  have := centered_finite ν hnorm s
  have : IsProbabilityMeasure (gaussianRows (d/16) d) := by unfold gaussianRows; infer_instance
  let B : ℝ := (boxScale (d/16) η).toReal^2*2^(2*(d/16))
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hb (X Z : Fin (d/16) → Fin d → ℝ) :
      mixedCubeAverage (centeredRho ν s) η X Z ≤ ENNReal.ofReal B := by
    calc
      _ ≤ boxScale (d/16) η^2*centeredRho ν s univ := mixedCube_le _ _ _ _
      _ ≤ boxScale (d/16) η^2*ENNReal.ofReal ((2:ℝ)^(2*(d/16))) :=
        mul_le_mul_right (centered_rho_mass ν hnorm s) _
      _ = _ := by
        dsimp [B]
        rw [ENNReal.ofReal_mul (by positivity),ENNReal.ofReal_pow ENNReal.toReal_nonneg,
          ENNReal.ofReal_toReal (boxScale_ne_top _ hη)]
  have h := fresh_weighted_log_moment (gaussianRows (d/16) d) (gaussianRows (d/16) d)
    u (fun t => mixedCubeAverage (centeredRho ν s) η t.1 t.2) hu (mixedCube_measurable _ _)
    hu0 hu1 hB (momentConstant_pos d L).le (by positivity : (0:ℝ) ≤ 2^(2*(d/16))) hb
    (d/16) (by omega) (centered_mixed_moment hd ν hH hν s hs L hL η hη)
  exact h.trans (add_le_add_right (mul_le_mul_of_nonneg_left (log_momentConstant d L hd)
    (integral_nonneg hu0)) _)

end KernelPotential.Noise

end OAI
