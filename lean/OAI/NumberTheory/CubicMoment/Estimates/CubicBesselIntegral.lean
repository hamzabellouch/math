import OAI.NumberTheory.CubicMoment.Estimates.RieszHeatKernel
import Mathlib.MeasureTheory.Integral.Prod

namespace OAI

/-! The fixed order-one-third Bessel kernel in the cubic theta expansion.
The Schläfli heat integral is used as the definition; its Mellin mass is
proved by absolute Fubini and the two ordinary Gamma integrals.
Normalization: NIST DLMF 10.32.10, specialized to nu=1/3 and positive
argument; the cubic theta expansion is DR v3 section 5.1, Eq.(5.6). -/
noncomputable section
open MeasureTheory Set
namespace CubicFirstMoment

/-- The positive heat integrand for `2*K_(1/3)(2*sqrt x)`. -/
def cubicBesselHeat (x t : ℝ) : ℝ :=
  t^(-4/3:ℝ)*Real.exp (-t)*Real.exp (-x/t)

/-- Fixed Bessel order required by the cubic metaplectic Fourier series. -/
def cubicBesselKernel (x : ℝ) : ℝ :=
  x^(1/6:ℝ)*∫ t in Ioi (0:ℝ), cubicBesselHeat x t

lemma cubicBesselHeat_nonneg {x t : ℝ} (ht : 0 < t) :
    0 ≤ cubicBesselHeat x t := by
  unfold cubicBesselHeat
  positivity

lemma integrable_inverse_laplace_rpow {a x : ℝ} (ha : 0 < a) (hx : 0 < x) :
    IntegrableOn (fun t : ℝ => t^(-a-1)*Real.exp (-x/t)) (Ioi 0) := by
  by_contra h
  have hp : 0 < Real.Gamma a*x^(-a) :=
    mul_pos (Real.Gamma_pos_of_pos ha) (Real.rpow_pos_of_pos hx _)
  rw [←inverse_gaussian_moment ha hx,integral_undef h] at hp
  exact lt_irrefl _ hp

lemma cubicBesselHeat_integrable {x : ℝ} (hx : 0 < x) :
    IntegrableOn (cubicBesselHeat x) (Ioi 0) := by
  have hi := integrable_inverse_laplace_rpow (by norm_num : (0:ℝ) < 1/3) hx
  have hm : AEStronglyMeasurable (cubicBesselHeat x) (volume.restrict (Ioi 0)) := by
    apply Measurable.aestronglyMeasurable
    unfold cubicBesselHeat
    fun_prop
  apply hi.mono' hm
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  change 0 < t at ht
  rw [Real.norm_eq_abs,abs_of_nonneg (cubicBesselHeat_nonneg ht)]
  change t^(-4/3:ℝ)*Real.exp (-t)*Real.exp (-x/t) ≤ _
  have he : Real.exp (-t) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith [ht])
  calc
    _ ≤ t^(-4/3:ℝ)*1*Real.exp (-x/t) := by gcongr
    _ = _ := by norm_num

lemma cubicBesselKernel_nonneg {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ cubicBesselKernel x := by
  unfold cubicBesselKernel
  apply mul_nonneg (Real.rpow_nonneg hx _) (setIntegral_nonneg measurableSet_Ioi ?_)
  intro t ht
  exact cubicBesselHeat_nonneg ht

lemma cubicBesselHeat_inner_integral {σ t : ℝ} (hσ : 1/6 < σ) (ht : 0 < t) :
    (∫ x in Ioi (0:ℝ), x^(σ+1/6-1)*cubicBesselHeat x t) =
      Real.Gamma (σ+1/6)*t^(σ-1/6-1)*Real.exp (-t) := by
  have ha : 0 < σ+1/6 := by linarith
  calc
    _ = (t^(-4/3:ℝ)*Real.exp (-t))*
        (∫ x in Ioi (0:ℝ), x^(σ+1/6-1)*Real.exp (-(1/t)*x)) := by
      rw [←integral_const_mul]
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x _
      dsimp only
      unfold cubicBesselHeat
      rw [show -(1/t)*x = -x/t by ring]
      ring
    _ = (t^(-4/3:ℝ)*Real.exp (-t))*(Real.Gamma (σ+1/6)*(1/t)^(-(σ+1/6))) := by
      rw [laplace_rpow ha (one_div_pos.mpr ht)]
    _ = _ := by
      have he : (1/t)^(-(σ+1/6)) = t^(σ+1/6) := by
        rw [one_div,←Real.rpow_neg_eq_inv_rpow,neg_neg]
      rw [he]
      calc
        _ = Real.Gamma (σ+1/6)*(t^(-4/3:ℝ)*t^(σ+1/6))*Real.exp (-t) := by ring
        _ = _ := by rw [←Real.rpow_add ht]; congr 2; ring_nf

lemma cubicBesselHeat_mellin_integrable {σ : ℝ} (hσ : 1/6 < σ) :
    Integrable (fun p : ℝ × ℝ => p.2^(σ+1/6-1)*cubicBesselHeat p.2 p.1)
      ((volume.restrict (Ioi 0)).prod (volume.restrict (Ioi 0))) := by
  have hm : AEStronglyMeasurable
      (fun p : ℝ × ℝ => p.2^(σ+1/6-1)*cubicBesselHeat p.2 p.1)
      ((volume.restrict (Ioi 0)).prod (volume.restrict (Ioi 0))) := by
    apply Measurable.aestronglyMeasurable
    unfold cubicBesselHeat
    fun_prop
  apply (integrable_prod_iff hm).mpr
  constructor
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have hi := (integrable_laplace_rpow (by linarith : 0 < σ+1/6)
      (one_div_pos.mpr ht)).const_mul (t^(-4/3:ℝ)*Real.exp (-t))
    apply hi.congr
    filter_upwards with x
    unfold cubicBesselHeat
    rw [show -(1/t)*x = -x/t by ring]
    ring
  · have hi := (integrable_laplace_rpow (by linarith : 0 < σ-1/6)
      (by norm_num : (0:ℝ) < 1)).const_mul (Real.Gamma (σ+1/6))
    apply hi.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rw [show (∫ x in Ioi (0:ℝ), ‖x^(σ+1/6-1)*cubicBesselHeat x t‖) =
        ∫ x in Ioi (0:ℝ), x^(σ+1/6-1)*cubicBesselHeat x t from ?_,
      cubicBesselHeat_inner_integral hσ ht]
    · simp only [neg_mul,one_mul,mul_assoc]
    · apply setIntegral_congr_fun measurableSet_Ioi
      intro x hx
      dsimp only
      rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (Real.rpow_nonneg hx.le _)
        (cubicBesselHeat_nonneg ht))]

/-- The Mellin mass needed to normalize the order-one-third theta kernel. -/
theorem cubicBesselKernel_real_mellin {σ : ℝ} (hσ : 1/6 < σ) :
    (∫ x in Ioi (0:ℝ), x^(σ-1)*cubicBesselKernel x) =
      Real.Gamma (σ+1/6)*Real.Gamma (σ-1/6) := by
  have hi := cubicBesselHeat_mellin_integrable hσ
  calc
    _ = ∫ x in Ioi (0:ℝ), ∫ t in Ioi (0:ℝ), x^(σ+1/6-1)*cubicBesselHeat x t := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x hx
      dsimp only
      unfold cubicBesselKernel
      rw [←mul_assoc,←Real.rpow_add hx,show σ-1+1/6=σ+1/6-1 by ring,
        ←integral_const_mul]
    _ = ∫ t in Ioi (0:ℝ), ∫ x in Ioi (0:ℝ), x^(σ+1/6-1)*cubicBesselHeat x t :=
      (integral_integral_swap hi).symm
    _ = ∫ t in Ioi (0:ℝ), Real.Gamma (σ+1/6)*t^(σ-1/6-1)*Real.exp (-t) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t ht
      exact cubicBesselHeat_inner_integral hσ ht
    _ = _ := by
      rw [show (fun t : ℝ => Real.Gamma (σ+1/6)*t^(σ-1/6-1)*Real.exp (-t)) =
        (fun t => Real.Gamma (σ+1/6)*(t^(σ-1/6-1)*Real.exp (-1*t))) by funext t; simp only [neg_mul,one_mul]; ring,
        integral_const_mul,laplace_rpow (by linarith : 0 < σ-1/6) (by norm_num : (0:ℝ) < 1)]
      simp

end CubicFirstMoment

end

end OAI
