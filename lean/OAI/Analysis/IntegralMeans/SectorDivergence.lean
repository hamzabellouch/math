import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace OAI

open MeasureTheory Set
open scoped ENNReal

namespace Brennan.Sector

theorem lintegral_inv_Ioo_eq_top (R : ℝ) (hR : 0 < R) :
    (∫⁻ r in Ioo (0 : ℝ) R, ENNReal.ofReal r⁻¹) = ⊤ := by
  by_contra h
  have hn : 0 ≤ᵐ[volume.restrict (Ioo (0 : ℝ) R)] (fun r : ℝ => r⁻¹) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
    exact inv_nonneg.mpr hr.1.le
  have hf : HasFiniteIntegral (fun r : ℝ => r⁻¹) (volume.restrict (Ioo (0 : ℝ) R)) :=
    (hasFiniteIntegral_iff_ofReal hn).2 (lt_top_iff_ne_top.mpr h)
  have hi : IntegrableOn (fun r : ℝ => r⁻¹) (Ioo (0 : ℝ) R) :=
    ⟨measurable_inv.aestronglyMeasurable, hf⟩
  have hp : IntegrableOn (fun r : ℝ => r ^ (-1 : ℝ)) (Ioo (0 : ℝ) R) := by
    simpa only [Real.rpow_neg_one] using hi
  exact (lt_irrefl (-1 : ℝ)) ((intervalIntegral.integrableOn_Ioo_rpow_iff hR).mp hp)

theorem lintegral_eq_top_of_sector_lower_bound (f : ℂ → ℝ≥0∞)
    (R a b c : ℝ) (hR : 0 < R) (hab : a < b) (hc : 0 < c)
    (ha : -Real.pi ≤ a) (hb : b ≤ Real.pi)
    (hlower : ∀ r ∈ Ioo (0 : ℝ) R, ∀ θ ∈ Ioo a b,
      ENNReal.ofReal (c / r ^ 2) ≤ f (Complex.polarCoord.symm (r, θ))) :
    (∫⁻ z, f z) = ⊤ := by
  let box : Set (ℝ × ℝ) := Ioo (0 : ℝ) R ×ˢ Ioo a b
  let radial : ℝ × ℝ → ℝ≥0∞ := fun p => ENNReal.ofReal c * ENNReal.ofReal p.1⁻¹
  have hradial : Measurable radial :=
    measurable_const.mul (ENNReal.measurable_ofReal.comp measurable_fst.inv)
  have hcinv : (∫⁻ r in Ioo (0 : ℝ) R, ENNReal.ofReal c * ENNReal.ofReal r⁻¹) = ⊤ := by
    have hmeas : Measurable (fun r : ℝ => ENNReal.ofReal r⁻¹) :=
      ENNReal.measurable_ofReal.comp measurable_inv
    rw [lintegral_const_mul (ENNReal.ofReal c) hmeas,
      lintegral_inv_Ioo_eq_top R hR,
      ENNReal.mul_top (ne_of_gt (ENNReal.ofReal_pos.mpr hc))]
  have hbox : (∫⁻ p in box, radial p) = ⊤ := by
    change (∫⁻ p in Ioo (0 : ℝ) R ×ˢ Ioo a b, radial p ∂volume.prod volume) = ⊤
    rw [setLIntegral_prod_symm _ hradial.aemeasurable]
    simp only [radial, hcinv]
    rw [lintegral_const, Measure.restrict_apply_univ, Real.volume_Ioo,
      ENNReal.top_mul (ne_of_gt (ENNReal.ofReal_pos.mpr (sub_pos.mpr hab)))]
  have hsub : box ⊆ polarCoord.target := by
    rw [polarCoord_target]
    intro p hp
    exact ⟨hp.1.1, lt_of_le_of_lt ha hp.2.1, lt_of_lt_of_le hp.2.2 hb⟩
  have hlower' (p : ℝ × ℝ) (hp : p ∈ box) :
      radial p ≤ ENNReal.ofReal p.1 • f (Complex.polarCoord.symm p) := by
    have hr : 0 < p.1 := hp.1.1
    have hid : ENNReal.ofReal c * ENNReal.ofReal p.1⁻¹ =
        ENNReal.ofReal p.1 * ENNReal.ofReal (c / p.1 ^ 2) := by
      rw [← ENNReal.ofReal_mul hc.le, ← ENNReal.ofReal_mul hr.le]
      congr 1
      field_simp [ne_of_gt hr]
    change ENNReal.ofReal c * ENNReal.ofReal p.1⁻¹ ≤
      ENNReal.ofReal p.1 * f (Complex.polarCoord.symm p)
    rw [hid]
    exact mul_le_mul_right (hlower p.1 hp.1 p.2 hp.2) _
  apply top_unique
  calc
    ⊤ = ∫⁻ p in box, radial p := hbox.symm
    _ ≤ ∫⁻ p in box, ENNReal.ofReal p.1 • f (Complex.polarCoord.symm p) :=
      setLIntegral_mono' (measurableSet_Ioo.prod measurableSet_Ioo) hlower'
    _ ≤ ∫⁻ p in polarCoord.target, ENNReal.ofReal p.1 • f (Complex.polarCoord.symm p) :=
      lintegral_mono_set hsub
    _ = ∫⁻ z, f z := Complex.lintegral_comp_polarCoord_symm f

end Brennan.Sector

end OAI
