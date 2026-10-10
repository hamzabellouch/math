import OAI.Analysis.CircleDomains.Sobolev.ACLWeakDerivatives
import Mathlib.MeasureTheory.Function.L2Space

namespace OAI

/-! ACL and an L² bound on the line derivatives produce an actual local
Sobolev gradient. All gradient fields here are constructed Borel functions. -/

open Set Filter MeasureTheory
open scoped ENNReal

noncomputable section

namespace CircleDomainRigidity

theorem rectangle_restrict_Ioo_eq_Icc (a b c d : ℝ) :
    (volume : Measure (ℝ × ℝ)).restrict (Ioo a b ×ˢ Ioo c d) =
      volume.restrict (Icc a b ×ˢ Icc c d) := by
  rw [Measure.volume_eq_prod]
  exact Measure.restrict_congr_set (Measure.set_prod_ae_eq Ioo_ae_eq_Icc Ioo_ae_eq_Icc)

theorem exists_rectangle_weak_gradient
    {f ρ : ℝ × ℝ → ℝ} {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d)
    (hf : MemLp f 2 (volume.restrict (Icc a b ×ˢ Icc c d)))
    (hρ : Measurable ρ) (hρ₂ : MemLp ρ 2 (volume.restrict (Icc a b ×ˢ Icc c d)))
    (hacx : ∀ᵐ y ∂volume.restrict (Icc c d),
      AbsolutelyContinuousOnInterval (fun x => f (x, y)) a b)
    (hacy : ∀ᵐ x ∂volume.restrict (Icc a b),
      AbsolutelyContinuousOnInterval (fun y => f (x, y)) c d)
    (hbx : ∀ᵐ y ∂volume.restrict (Icc c d), ∀ᵐ x ∂volume.restrict (Icc a b),
      |deriv (fun t => f (t, y)) x| ≤ ρ (x, y))
    (hby : ∀ᵐ x ∂volume.restrict (Icc a b), ∀ᵐ y ∂volume.restrict (Icc c d),
      |deriv (fun t => f (x, t)) y| ≤ ρ (x, y)) :
    ∃ Gx Gy : ℝ × ℝ → ℝ, Measurable Gx ∧ Measurable Gy ∧
      MemLp Gx 2 (volume.restrict (Icc a b ×ˢ Icc c d)) ∧
      MemLp Gy 2 (volume.restrict (Icc a b ×ˢ Icc c d)) ∧
      (∀ᵐ p ∂volume.restrict (Icc a b ×ˢ Icc c d), |Gx p| ≤ ρ p ∧ |Gy p| ≤ ρ p) ∧
      ∀ φ : ℝ × ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
        tsupport φ ⊆ Ioo a b ×ˢ Ioo c d →
        (∫p in Icc a b ×ˢ Icc c d, f p * (fderiv ℝ φ p) (1, 0)) =
          -(∫p in Icc a b ×ˢ Icc c d, Gx p * φ p) ∧
        (∫p in Icc a b ×ˢ Icc c d, f p * (fderiv ℝ φ p) (0, 1)) =
          -(∫p in Icc a b ×ˢ Icc c d, Gy p * φ p) := by
  let : IsFiniteMeasure ((volume : Measure (ℝ × ℝ)).restrict (Icc a b ×ˢ Icc c d)) :=
    isFiniteMeasure_restrict.mpr (isCompact_Icc.prod isCompact_Icc).measure_lt_top.ne
  have hfmeas : AEStronglyMeasurable f (volume.restrict (Ioo a b ×ˢ Ioo c d)) := by
    rw [rectangle_restrict_Ioo_eq_Icc]
    exact hf.aestronglyMeasurable
  obtain ⟨Gx, hGx, hrx⟩ := exists_measurable_horizontal_derivative f hfmeas hacx
  obtain ⟨Gy, hGy, hry⟩ := exists_measurable_vertical_derivative f hfmeas hacy
  have hx : ∀ᵐ y ∂volume.restrict (Icc c d), ∀ᵐ x ∂volume.restrict (Icc a b),
      |Gx (x, y)| ≤ ρ (x, y) := by
    filter_upwards [hrx, hbx] with y hy hb
    filter_upwards [hy, hb] with x hx hb
    simpa only [hx] using hb
  have hy : ∀ᵐ x ∂volume.restrict (Icc a b), ∀ᵐ y ∂volume.restrict (Icc c d),
      |Gy (x, y)| ≤ ρ (x, y) := by
    filter_upwards [hry, hby] with x hx hb
    filter_upwards [hx, hb] with y hy hb
    simpa only [hy] using hb
  have hmeasx : MeasurableSet {p : ℝ × ℝ | |Gx p| ≤ ρ p} :=
    by simpa only [Real.norm_eq_abs] using measurableSet_le hGx.norm hρ
  have hmeasy : MeasurableSet {p : ℝ × ℝ | |Gy p| ≤ ρ p} :=
    by simpa only [Real.norm_eq_abs] using measurableSet_le hGy.norm hρ
  have hBx : ∀ᵐ p ∂volume.restrict (Icc a b ×ˢ Icc c d), |Gx p| ≤ ρ p := by
    rw [Measure.volume_eq_prod, ← Measure.prod_restrict]
    exact (Measure.ae_prod_iff_ae_ae hmeasx).2 ((Measure.ae_ae_comm hmeasx).2 hx)
  have hBy : ∀ᵐ p ∂volume.restrict (Icc a b ×ˢ Icc c d), |Gy p| ≤ ρ p := by
    rw [Measure.volume_eq_prod, ← Measure.prod_restrict]
    exact (Measure.ae_prod_iff_ae_ae hmeasy).2 hy
  have hx₂ : MemLp Gx 2 (volume.restrict (Icc a b ×ˢ Icc c d)) :=
    hρ₂.of_le hGx.aestronglyMeasurable (hBx.mono fun p hp => by
      simpa only [Real.norm_eq_abs] using hp.trans (le_abs_self _))
  have hy₂ : MemLp Gy 2 (volume.restrict (Icc a b ×ˢ Icc c d)) :=
    hρ₂.of_le hGy.aestronglyMeasurable (hBy.mono fun p hp => by
      simpa only [Real.norm_eq_abs] using hp.trans (le_abs_self _))
  refine ⟨Gx, Gy, hGx, hGy, hx₂, hy₂, hBx.and hBy, ?_⟩
  intro φ hφ hs hsub
  exact ⟨integral_mul_horizontal_deriv_eq_neg hab (hf.integrable (by norm_num))
    (hx₂.integrable (by norm_num)) hacx hrx hφ hs hsub,
    integral_mul_vertical_deriv_eq_neg hcd (hf.integrable (by norm_num))
    (hy₂.integrable (by norm_num)) hacy hry hφ hs hsub⟩

end CircleDomainRigidity

end

end OAI
