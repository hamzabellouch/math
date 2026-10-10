import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialFreeComponents
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

namespace OAI

/-! Quantitative bootstrap on the short free shell: |F′|≤.35(r-l), |F-1|≤.175(r-l)². -/

open Set MeasureTheory Filter
namespace DefocusingNLS

theorem radialFreeForcing_norm (b r : ℝ)
    (hb : b ∈ Icc (334/1000 : ℝ) (335/1000)) (hr : r ∈ Icc (3 : ℝ) (10/3))
    (z w : ℂ) : ‖-radialFreeCoefficient r*w-(b : ℂ)*z‖ ≤ 6*‖w‖+(335/1000 : ℝ)*‖z‖ := by
  have hbn : ‖(b : ℂ)‖ ≤ (335/1000 : ℝ) := by
    rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (by linarith [hb.1])]
    exact hb.2
  calc
    _ ≤ ‖-radialFreeCoefficient r*w‖+‖(b : ℂ)*z‖ := norm_sub_le _ _
    _ = ‖radialFreeCoefficient r‖*‖w‖+‖(b : ℂ)‖*‖z‖ := by rw [norm_mul,norm_neg,norm_mul]
    _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_right (radialFreeCoefficient_norm r hr) (norm_nonneg w))
      (mul_le_mul_of_nonneg_right hbn (norm_nonneg z))

theorem radial_complex_integral_bound (l r C : ℝ) (hlr : l ≤ r) (f : ℝ → ℂ)
    (hf : ∀ t ∈ Icc l r, ‖f t‖ ≤ C) : ‖∫ t in l..r, f t‖ ≤ C*(r-l) := by
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (fun t ht =>
    hf t ⟨(uIoc_of_le hlr ▸ ht).1.le,(uIoc_of_le hlr ▸ ht).2⟩)
  simpa only [abs_of_nonneg (sub_nonneg.mpr hlr)] using h

theorem radial_free_short_bounds (b l u : ℝ)
    (hb : b ∈ Icc (334/1000 : ℝ) (335/1000)) (hl : (3 : ℝ) ≤ l)
    (hu : u ≤ (10/3 : ℝ)) (_hlu : l ≤ u) (hwidth : u-l ≤ (1/1000 : ℝ))
    (F G : ℝ → ℂ)
    (hF : ∀ r ∈ Icc l u, F r=1+∫ t in l..r, G t)
    (hG : ∀ r ∈ Icc l u, G r=∫ t in l..r, -radialFreeCoefficient t*G t-(b : ℂ)*F t)
    (hB : ∀ r ∈ Icc l u, ‖F r‖ ≤ 2 ∧ ‖G r‖ ≤ 2) :
    ∀ r ∈ Icc l u, ‖G r‖ ≤ (35/100 : ℝ)*(r-l) ∧
      ‖F r-1‖ ≤ (175/1000 : ℝ)*(r-l)^2 := by
  have hs (r : ℝ) (hr : r ∈ Icc l u) : r ∈ Icc (3 : ℝ) (10/3) :=
    ⟨hl.trans hr.1,hr.2.trans hu⟩
  have hg₁ : ∀ r ∈ Icc l u, ‖G r‖ ≤ 14*(r-l) := by
    intro r hr
    rw [hG r hr]
    apply radial_complex_integral_bound l r 14 hr.1
    intro t ht
    have htU : t ∈ Icc l u := ⟨ht.1,ht.2.trans hr.2⟩
    have h := radialFreeForcing_norm b t hb (hs t htU) (F t) (G t)
    have hf := (hB t htU).1
    have hg := (hB t htU).2
    linarith
  have hf₁ : ∀ r ∈ Icc l u, ‖F r-1‖ ≤ (14/1000 : ℝ)*(r-l) := by
    intro r hr
    have he : F r-1=∫ t in l..r, G t := by rw [hF r hr]; ring
    rw [he]
    apply radial_complex_integral_bound l r (14/1000) hr.1
    intro t ht
    have hg := hg₁ t ⟨ht.1,ht.2.trans hr.2⟩
    have hw : t-l ≤ (1/1000 : ℝ) := by linarith [ht.2,hr.2]
    linarith
  have hf₂ : ∀ r ∈ Icc l u, ‖F r‖ ≤ 1+(14/1000000 : ℝ) := by
    intro r hr
    have hn : ‖F r‖ ≤ ‖F r-1‖+1 := by
      have h := norm_add_le (F r-1) (1 : ℂ)
      simpa only [sub_add_cancel,norm_one] using h
    have hf := hf₁ r hr
    have hw : r-l ≤ (1/1000 : ℝ) := by linarith [hr.2]
    linarith
  have hg₂ : ∀ r ∈ Icc l u, ‖G r‖ ≤ (42/100 : ℝ)*(r-l) := by
    intro r hr
    rw [hG r hr]
    apply radial_complex_integral_bound l r (42/100) hr.1
    intro t ht
    have htU : t ∈ Icc l u := ⟨ht.1,ht.2.trans hr.2⟩
    have hg := hg₁ t htU
    have hw : t-l ≤ (1/1000 : ℝ) := by linarith [ht.2,hr.2]
    have hf := hf₂ t htU
    have hn := radialFreeForcing_norm b t hb (hs t htU) (F t) (G t)
    linarith
  have hg₃ : ∀ r ∈ Icc l u, ‖G r‖ ≤ (35/100 : ℝ)*(r-l) := by
    intro r hr
    rw [hG r hr]
    apply radial_complex_integral_bound l r (35/100) hr.1
    intro t ht
    have htU : t ∈ Icc l u := ⟨ht.1,ht.2.trans hr.2⟩
    have hg := hg₂ t htU
    have hw : t-l ≤ (1/1000 : ℝ) := by linarith [ht.2,hr.2]
    have hf := hf₂ t htU
    have hn := radialFreeForcing_norm b t hb (hs t htU) (F t) (G t)
    linarith
  intro r hr
  refine ⟨hg₃ r hr,?_⟩
  have he : F r-1=∫ t in l..r, G t := by rw [hF r hr]; ring
  rw [he]
  have hi : (∫ t in l..r, (35/100 : ℝ)*(t-l))=(175/1000 : ℝ)*(r-l)^2 := by
    rw [intervalIntegral.integral_const_mul,intervalIntegral.integral_sub (f := fun t : ℝ => t) (g := fun _ : ℝ => l)
      (continuous_id.intervalIntegrable l r) (continuous_const.intervalIntegrable l r),
      integral_id,intervalIntegral.integral_const]
    simp only [smul_eq_mul]
    ring
  rw [← hi]
  apply intervalIntegral.norm_integral_le_of_norm_le hr.1
    (Eventually.of_forall (fun t ht => hg₃ t ⟨ht.1.le,ht.2.trans hr.2⟩))
    ((continuous_const.mul (continuous_id.sub continuous_const)).intervalIntegrable l r)

end DefocusingNLS

end OAI
