import OAI.Analysis.CircleDomains.Sobolev.L2SummableMajorant

namespace OAI

/-! A scalar L2 majorant bounds the differential error of the actual
priority interpolation. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem l2_norm_le_of_additive_majorant
    {U : Set ℂ} {D : ℂ → (ℂ →L[ℝ] ℝ)} {g h : ℂ → ℝ} {a : ℝ}
    (ha : 0 ≤ a) (hD : AEStronglyMeasurable D (volume.restrict U))
    (hg : MemLp g 2 (volume.restrict U)) (hh : MemLp h 2 (volume.restrict U))
    (hg0 : ∀ᵐ z ∂volume.restrict U, 0 ≤ g z)
    (hh0 : ∀ᵐ z ∂volume.restrict U, 0 ≤ h z)
    (hbound : ∀ᵐ z ∂volume.restrict U, ‖D z‖ ≤ a*g z+h z) :
    MemLp D 2 (volume.restrict U) ∧
      (eLpNorm D 2 (volume.restrict U)).toReal ≤
        a*(eLpNorm g 2 (volume.restrict U)).toReal +
          (eLpNorm h 2 (volume.restrict U)).toReal := by
  let v : ℂ → ℝ := fun z => a*g z+h z
  have hv : MemLp v 2 (volume.restrict U) := (hg.const_mul a).add hh
  have hb : ∀ᵐ z ∂volume.restrict U, ‖D z‖ ≤ ‖v z‖ := by
    filter_upwards [hbound, hg0, hh0] with z hz hzg hzh
    simpa only [v, Real.norm_eq_abs, abs_of_nonneg (add_nonneg (mul_nonneg ha hzg) hzh)] using hz
  have hd := hv.of_le hD hb
  refine ⟨hd, ?_⟩
  apply (ENNReal.toReal_mono hv.ne_top (eLpNorm_mono_ae hD hb)).trans
  have hsum := eLpNorm_add_le (μ := volume.restrict U) (p := 2)
    (f := fun z => a*g z) (g := h) (by norm_num)
  have hh' : eLpNorm (fun z => a*g z) 2 (volume.restrict U) ≠ ∞ := (hg.const_mul a).ne_top
  have hreal := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hh', hh.ne_top⟩) hsum
  rw [ENNReal.toReal_add hh' hh.ne_top] at hreal
  have he : eLpNorm (fun z => a*g z) 2 (volume.restrict U) =
      ENNReal.ofReal a * eLpNorm g 2 (volume.restrict U) := by
    change eLpNorm (a • g) 2 (volume.restrict U) = _
    simpa only [Real.enorm_eq_ofReal_abs, abs_of_nonneg ha] using
      eLpNorm_const_smul a g 2 (volume.restrict U)
  rw [he, ENNReal.toReal_mul, ENNReal.toReal_ofReal ha] at hreal
  exact hreal

end CircleDomainRigidity

end

end OAI
