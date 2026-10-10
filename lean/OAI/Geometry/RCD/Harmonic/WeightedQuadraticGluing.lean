import OAI.Geometry.RCD.Transport.BrokenGeodesicCost
import OAI.Analysis.RCDHeat.ExistingAnalytic

namespace OAI

/-! # Sharp gluing saturation at an arbitrary interior time -/

open Set Filter MeasureTheory
open scoped ENNReal
noncomputable section
namespace RegularPointCoordinates

theorem weighted_quadratic_gluing_saturation {A : Type*} [MeasurableSpace A]
    (μ : Measure A) (a b c : A → ℝ) (ha : Measurable a) (hb : Measurable b)
    (han : ∀ᵐ x ∂μ, 0 ≤ a x) (hbn : ∀ᵐ x ∂μ, 0 ≤ b x)
    (hcn : ∀ᵐ x ∂μ, 0 ≤ c x) (htri : ∀ᵐ x ∂μ, c x ≤ a x + b x)
    {t : ℝ} (ht : 0 < t) (ht1 : t < 1) (C : ℝ≥0∞) (hC : C ≠ ∞)
    (h0 : ∫⁻ x, ENNReal.ofReal (a x)^2 ∂μ ≤ ENNReal.ofReal t^2*C)
    (h1 : ∫⁻ x, ENNReal.ofReal (b x)^2 ∂μ ≤ ENNReal.ofReal (1-t)^2*C)
    (hmin : C ≤ ∫⁻ x, ENNReal.ofReal (c x)^2 ∂μ) :
    (∫⁻ x, ENNReal.ofReal (c x)^2 ∂μ)=C ∧
      ∀ᵐ x ∂μ, a x=t*c x ∧ b x=(1-t)*c x := by
  have hu : 0 < 1-t := sub_pos.mpr ht1
  let f := fun x => ENNReal.ofReal (c x)^2
  let g := fun x => ENNReal.ofReal t⁻¹*ENNReal.ofReal (a x)^2+
    ENNReal.ofReal (1-t)⁻¹*ENNReal.ofReal (b x)^2
  have hg : Measurable g :=
    ((ha.ennreal_ofReal.pow_const 2).const_mul _).add
      ((hb.ennreal_ofReal.pow_const 2).const_mul _)
  have hge (x : A) (hax : 0 ≤ a x) (hbx : 0 ≤ b x) :
      g x=ENNReal.ofReal ((a x)^2/t+(b x)^2/(1-t)) := by
    dsimp only [g]
    rw [← ENNReal.ofReal_pow hax,← ENNReal.ofReal_pow hbx,
      ← ENNReal.ofReal_mul (inv_nonneg.mpr ht.le),
      ← ENNReal.ofReal_mul (inv_nonneg.mpr hu.le),
      ← ENNReal.ofReal_add (by positivity) (by positivity)]
    congr 1
    ring
  have hfg : f ≤ᵐ[μ] g := by
    filter_upwards [han,hbn,hcn,htri] with x hax hbx hcx hx
    rw [hge x hax hbx]
    dsimp only [f]
    rw [← ENNReal.ofReal_pow hcx]
    apply ENNReal.ofReal_le_ofReal
    have hh := two_leg_cost_nonneg hax hbx hcx hx ht ht1
    linarith only [hh]
  have hta : ENNReal.ofReal t⁻¹*ENNReal.ofReal t^2=ENNReal.ofReal t := by
    rw [← ENNReal.ofReal_pow ht.le,← ENNReal.ofReal_mul (inv_nonneg.mpr ht.le)]
    congr 1
    field_simp
  have htb : ENNReal.ofReal (1-t)⁻¹*ENNReal.ofReal (1-t)^2=ENNReal.ofReal (1-t) := by
    rw [← ENNReal.ofReal_pow hu.le,← ENNReal.ofReal_mul (inv_nonneg.mpr hu.le)]
    congr 1
    field_simp
  have hgc : ∫⁻ x, g x ∂μ ≤ C := by
    dsimp only [g]
    rw [lintegral_add_left ((ha.ennreal_ofReal.pow_const 2).const_mul _),
      lintegral_const_mul _ (ha.ennreal_ofReal.pow_const 2),
      lintegral_const_mul _ (hb.ennreal_ofReal.pow_const 2)]
    calc
      _ ≤ ENNReal.ofReal t⁻¹*(ENNReal.ofReal t^2*C)+
          ENNReal.ofReal (1-t)⁻¹*(ENNReal.ofReal (1-t)^2*C) := by gcongr
      _ = C := by
        rw [← mul_assoc,← mul_assoc,hta,htb,← add_mul,
          ← ENNReal.ofReal_add ht.le hu.le]
        simp
  have hfc : ∫⁻ x, f x ∂μ ≠ ∞ :=
    ne_top_of_le_ne_top hC ((lintegral_mono_ae hfg).trans hgc)
  have he := ae_eq_of_ae_le_of_lintegral_le hfg hfc hg.aemeasurable (hgc.trans hmin)
  refine ⟨le_antisymm ((lintegral_mono_ae hfg).trans hgc) hmin,?_⟩
  filter_upwards [han,hbn,hcn,htri,he] with x hax hbx hcx hx heq
  rw [hge x hax hbx] at heq
  dsimp only [f] at heq
  rw [← ENNReal.ofReal_pow hcx] at heq
  have hr : (c x)^2=(a x)^2/t+(b x)^2/(1-t) := by
    have hh := congrArg ENNReal.toReal heq
    rwa [ENNReal.toReal_ofReal (sq_nonneg _),ENNReal.toReal_ofReal (by positivity)] at hh
  exact two_leg_cost_zero hax hbx hcx hx ht ht1 (by linarith only [hr])

end RegularPointCoordinates

end

end OAI
