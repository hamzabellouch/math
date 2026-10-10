import Mathlib

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
open MeasureTheory Filter Complex TopologicalSpace
open scoped Topology InnerProductSpace ENNReal
open MeasureTheory Filter Complex
open scoped Topology BigOperators ComplexConjugate FourierTransform SchwartzMap ENNReal
open MeasureTheory Filter
open scoped Topology ContDiff SchwartzMap FourierTransform ENNReal
open MeasureTheory Filter
open scoped ContDiff InnerProductSpace Topology
open MeasureTheory Filter
open scoped ENNReal
open MeasureTheory Set Metric
open scoped ENNReal
namespace CoulombDensity
abbrev Space := EuclideanSpace ℝ (Fin 3)

lemma young_density {ρ v ε : ℝ} (hρ : 0 ≤ ρ) (hv : 0 ≤ v) (hε : 0 < ε) :
    ρ*v ≤ ε*ρ^(5/3:ℝ) + ε^(-3/2:ℝ)*v^(5/2:ℝ) := by
  have hpq : (5/3:ℝ).HolderConjugate (5/2:ℝ) := by
    rw [Real.holderConjugate_iff]; norm_num
  have h := Real.young_inequality_of_nonneg
    (mul_nonneg (Real.rpow_nonneg hε.le (3/5:ℝ)) hρ)
    (mul_nonneg (Real.rpow_nonneg hε.le (-3/5:ℝ)) hv) hpq
  have he1 : (ε^(3/5:ℝ)*ρ)^(5/3:ℝ) = ε*ρ^(5/3:ℝ) := by
    rw [Real.mul_rpow (by positivity) hρ,← Real.rpow_mul hε.le]
    norm_num
  have he2 : (ε^(-3/5:ℝ)*v)^(5/2:ℝ) = ε^(-3/2:ℝ)*v^(5/2:ℝ) := by
    rw [Real.mul_rpow (by positivity) hv,← Real.rpow_mul hε.le]
    norm_num
  have he3 : (ε^(3/5:ℝ)*ρ)*(ε^(-3/5:ℝ)*v) = ρ*v := by
    calc
      _ = (ε^(3/5:ℝ)*ε^(-3/5:ℝ))*(ρ*v) := by ring
      _ = _ := by rw [← Real.rpow_add hε]; norm_num
  rw [he1,he2,he3] at h
  have h1 := Real.rpow_nonneg hρ (5/3:ℝ)
  have h2 := mul_nonneg (Real.rpow_nonneg hε.le (-3/2:ℝ)) (Real.rpow_nonneg hv (5/2:ℝ))
  nlinarith

lemma radial_power_identity {y : ℝ} (hy : 0 < y) :
    y^2*y^(-5/2:ℝ) = y^(-1/2:ℝ) := by
  rw [← Real.rpow_natCast y 2,← Real.rpow_add hy]
  norm_num

lemma integrable_ball_kernel {R : ℝ} (_hR : 0 ≤ R) :
    IntegrableOn (fun x : Space => ‖x‖^(-5/2:ℝ)) (ball 0 R) := by
  apply (integrableOn_fun_norm_addHaar (volume : Measure Space) (f := fun r : ℝ => r^(-5/2:ℝ))).mpr
  simp only [Space,finrank_euclideanSpace_fin,Nat.reduceSub,smul_eq_mul]
  apply (intervalIntegral.intervalIntegrable_rpow' (by norm_num : (-1:ℝ) < -1/2) (a := 0) (b := R)).1.mono_set (by
    intro x hx; exact ⟨hx.1,hx.2.le⟩) |>.congr_fun _ measurableSet_Ioo
  intro x hx
  exact (radial_power_identity hx.1).symm

lemma integral_ball_kernel {R : ℝ} (hR : 0 ≤ R) :
    (∫ x : Space in ball 0 R, ‖x‖^(-5/2:ℝ)) = 8*Real.pi*R^(1/2:ℝ) := by
  rw [← integral_indicator measurableSet_ball]
  have he : (ball (0 : Space) R).indicator (fun x => ‖x‖^(-5/2:ℝ)) =
      fun x => (Iio R).indicator (fun t : ℝ => t^(-5/2:ℝ)) ‖x‖ := by
    ext x
    simp [Set.indicator,dist_zero_right]
  rw [he,integral_fun_norm_addHaar (volume : Measure Space)]
  have hu : (volume : Measure Space).real (ball 0 1) = Real.pi*4/3 := by
    rw [Measure.real,EuclideanSpace.volume_ball_fin_three]
    norm_num [ENNReal.toReal_ofReal (by positivity : 0 ≤ Real.pi*4/3)]
  simp only [Space,finrank_euclideanSpace_fin,hu,nsmul_eq_mul,
    Nat.cast_ofNat,Nat.reduceSub,smul_eq_mul]
  have he' : (∫ y : ℝ in Ioi 0, y^2*(Iio R).indicator (fun t => t^(-5/2:ℝ)) y) =
      ∫ y : ℝ in Ioo 0 R, y^(-1/2:ℝ) := by
    calc
      _ = ∫ y : ℝ in Ioi 0, (Iio R).indicator (fun t => t^(-1/2:ℝ)) y := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro y hy
        by_cases hr : y < R
        · simp only [Set.indicator, mem_Iio, ite_eq_left hr]; exact radial_power_identity hy
        · simp only [Set.indicator, mem_Iio, ite_eq_right hr,mul_zero]
      _ = _ := by
        rw [integral_indicator measurableSet_Iio,Measure.restrict_restrict measurableSet_Iio]
        have hi : Iio R ∩ Ioi (0 : ℝ) = Ioo 0 R := by ext x; simp [and_comm]
        rw [hi]
  rw [he',← integral_Ioc_eq_integral_Ioo,← intervalIntegral.integral_of_le hR,
    integral_rpow (Or.inl (by norm_num : (-1:ℝ) < -1/2))]
  norm_num
  ring
lemma nuclear_pointwise {ρ Z ε R : ℝ} (hρ : 0 ≤ ρ) (hZ : 0 ≤ Z)
    (hε : 0 < ε) (hR : 0 < R) (x : Space) :
    ρ * (Z / ‖x‖) ≤ ε*ρ^(5/3:ℝ) +
      (ε^(-3/2:ℝ)*Z^(5/2:ℝ)) *
        (ball (0 : Space) R).indicator (fun y => ‖y‖^(-5/2:ℝ)) x + (Z/R)*ρ := by
  by_cases hx : ‖x‖ < R
  · have hy := young_density hρ (div_nonneg hZ (norm_nonneg x)) hε
    have he : (Z/‖x‖)^(5/2:ℝ) = Z^(5/2:ℝ)*‖x‖^(-5/2:ℝ) := by
      rw [Real.div_rpow hZ (norm_nonneg x),show (-5/2:ℝ) = -(5/2:ℝ) by ring,
        Real.rpow_neg (norm_nonneg x),div_eq_mul_inv]
    rw [he] at hy
    have hm : x ∈ ball (0 : Space) R := by simpa only [mem_ball,dist_zero_right] using hx
    rw [indicator_of_mem hm]
    have hp : 0 ≤ (Z/R)*ρ := by positivity
    nlinarith
  · have hx' : R ≤ ‖x‖ := le_of_not_gt hx
    have hm : x ∉ ball (0 : Space) R := by simpa only [mem_ball,dist_zero_right] using hx
    rw [indicator_of_notMem hm,mul_zero,add_zero]
    have hl : Z/‖x‖ ≤ Z/R := div_le_div_of_nonneg_left hZ hR hx'
    have hp : 0 ≤ ε*ρ^(5/3:ℝ) := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hl hρ]

lemma nuclear_density_bound (ρ : Space → ℝ) (hρ : ∀ x, 0 ≤ ρ x)
    (hm : Integrable ρ) (hd : Integrable (fun x => ρ x^(5/3:ℝ)))
    {Z ε R : ℝ} (hZ : 0 ≤ Z) (hε : 0 < ε) (hR : 0 < R) :
    Integrable (fun x => ρ x*(Z/‖x‖)) ∧
    (∫ x, ρ x*(Z/‖x‖)) ≤ ε*(∫ x, ρ x^(5/3:ℝ)) +
      8*Real.pi*ε^(-3/2:ℝ)*Z^(5/2:ℝ)*R^(1/2:ℝ) + (Z/R)*(∫ x, ρ x) := by
  let K : Space → ℝ := (ball (0 : Space) R).indicator (fun y => ‖y‖^(-5/2:ℝ))
  have hk : Integrable K := (integrable_indicator_iff measurableSet_ball).mpr
    (integrable_ball_kernel hR.le)
  have hg : Integrable (fun x => ε*ρ x^(5/3:ℝ) +
      (ε^(-3/2:ℝ)*Z^(5/2:ℝ))*K x + (Z/R)*ρ x) :=
    ((hd.const_mul ε).add (hk.const_mul _)).add (hm.const_mul _)
  have hb (x : Space) := nuclear_pointwise (hρ x) hZ hε hR x
  have hf : Integrable (fun x => ρ x*(Z/‖x‖)) :=
    hg.mono' (hm.aestronglyMeasurable.mul
      ((measurable_const.div measurable_norm).aestronglyMeasurable))
      (Filter.Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (hρ x) (by positivity))]
        exact hb x)
  refine ⟨hf, ?_⟩
  calc
    _ ≤ ∫ x, ε*ρ x^(5/3:ℝ) + (ε^(-3/2:ℝ)*Z^(5/2:ℝ))*K x + (Z/R)*ρ x :=
      integral_mono hf hg hb
    _ = _ := by
      rw [integral_add (f := fun x => ε*ρ x^(5/3:ℝ) + (ε^(-3/2:ℝ)*Z^(5/2:ℝ))*K x)
        ((hd.const_mul ε).add (hk.const_mul (ε^(-3/2:ℝ)*Z^(5/2:ℝ)))) (hm.const_mul (Z/R)),
        integral_add (hd.const_mul ε) (hk.const_mul (ε^(-3/2:ℝ)*Z^(5/2:ℝ))),
        integral_const_mul,integral_const_mul,integral_const_mul]
      have ih : (∫ x, K x) = 8*Real.pi*R^(1/2:ℝ) := by
        rw [show K = (ball (0 : Space) R).indicator (fun y => ‖y‖^(-5/2:ℝ)) from rfl,
          integral_indicator measurableSet_ball,integral_ball_kernel hR.le]
      rw [ih]
      ring
lemma nuclear_scale {Z : ℝ} (hZ : 0 < Z) :
    Z^(5/2:ℝ)*(Z^(-1/3:ℝ))^(1/2:ℝ) = Z^(7/3:ℝ) ∧
    Z / Z^(-1/3:ℝ) * (3*Z) = 3*Z^(7/3:ℝ) := by
  constructor
  · rw [← Real.rpow_mul hZ.le,← Real.rpow_add hZ]
    congr 1
    ring
  · have he : Z / Z^(-1/3:ℝ) = Z^(4/3:ℝ) := by
      calc
        _ = Z^(1:ℝ) / Z^(-1/3:ℝ) := by rw [Real.rpow_one]
        _ = _ := by rw [← Real.rpow_sub hZ]; congr 1; ring
    rw [he]
    calc
      _ = 3*(Z^(4/3:ℝ)*Z^(1:ℝ)) := by rw [Real.rpow_one]; ring
      _ = _ := by rw [← Real.rpow_add hZ]; congr 2; ring

lemma nuclear_density_scaled (ρ : Space → ℝ) (hρ : ∀ x, 0 ≤ ρ x)
    (hm : Integrable ρ) (hd : Integrable (fun x => ρ x^(5/3:ℝ)))
    {Z ε : ℝ} (hZ : 0 < Z) (hε : 0 < ε) (hmass : (∫ x, ρ x) ≤ 3*Z) :
    (∫ x, ρ x*(Z/‖x‖)) ≤ ε*(∫ x, ρ x^(5/3:ℝ)) +
      (8*Real.pi*ε^(-3/2:ℝ) + 3)*Z^(7/3:ℝ) := by
  have h := (nuclear_density_bound ρ hρ hm hd hZ.le hε
    (Real.rpow_pos_of_pos hZ (-1/3:ℝ))).2
  have hn : (Z/Z^(-1/3:ℝ))*(∫ x, ρ x) ≤ (Z/Z^(-1/3:ℝ))*(3*Z) :=
    mul_le_mul_of_nonneg_left hmass (by positivity)
  rcases nuclear_scale hZ with ⟨hs,ht⟩
  have ha : 8*Real.pi*ε^(-3/2:ℝ)*Z^(5/2:ℝ)*(Z^(-1/3:ℝ))^(1/2:ℝ) =
      (8*Real.pi*ε^(-3/2:ℝ))*Z^(7/3:ℝ) := by
    rw [mul_assoc,hs]
  rw [ha] at h
  rw [ht] at hn
  nlinarith
end CoulombDensity

end

end OAI
