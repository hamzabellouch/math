import OAI.Analysis.LipschitzHilbert.Fourier.LineCommutatorDerivative
import OAI.Analysis.LipschitzHilbert.Fourier.LineGeometricSchur

namespace OAI

/-! The differentiated comparable-frequency commutator has no output
above a fixed multiple of its input frequencies. -/
noncomputable section
open scoped FourierTransform
namespace LipschitzHilbert.PacketRepresentation
open DyadicLineGrid

theorem lineScaleWeight_symm (i j : ℤ) : lineScaleWeight i j=lineScaleWeight j i := by
  unfold lineScaleWeight
  rw [←Int.natAbs_neg,neg_sub]

theorem bounded_scaleRatio_le_weight (i k : ℤ) (h : scale k/scale i≤128) :
    scale k/scale i≤16384*lineScaleWeight i k := by
  by_cases hki : k ≤ i
  · rw [lineScaleWeight_ratio k i hki,lineScaleWeight_symm k i]
    nlinarith [lineScaleWeight_pos i k]
  · have hik : i≤k := by omega
    have hw : (scale k/scale i)*lineScaleWeight i k=1 := by
      rw [←lineScaleWeight_ratio i k hik]
      field_simp [(scale_pos i).ne',(scale_pos k).ne']
    have hh := mul_le_mul_of_nonneg_right h (lineScaleWeight_pos i k).le
    rw [hw] at hh
    linarith

theorem comparableDerivative_projection_zero (m b h : SchwartzMap ℝ ℂ)
    (W V : ℝ) (hW : 0<W) (hV : 0<V) (hWV : 128*V≤W)
    (hh : ∀ eta, (𝓕 h : SchwartzMap ℝ ℂ) eta≠0 → |eta|≤64/W) :
    let B := lineSchwartzProjection dyadicDifference W hW.ne' b
    lineSchwartzProjection dyadicDifference V hV.ne'
      (schwartzDerivative 1 (lineSchwartzCommutator m B h))=0 := by
  intro B
  apply (FourierTransform.fourierEquiv ℂ (SchwartzMap ℝ ℂ)).injective
  ext eta
  change (𝓕 (lineSchwartzProjection dyadicDifference V hV.ne'
    (schwartzDerivative 1 (lineSchwartzCommutator m B h))) : SchwartzMap ℝ ℂ) eta=(𝓕 (0 : SchwartzMap ℝ ℂ)) eta
  rw [FourierTransform.fourier_zero,zero_apply]
  by_contra hne
  have hd := dyadicProjection_frequency V hV (schwartzDerivative 1 (lineSchwartzCommutator m B h)) eta hne
  have hf := lineSchwartzProjection_frequency_of_nonzero dyadicDifference _ V hV.ne' eta hne
  have hc := schwartzDerivative_frequency_of_nonzero (lineSchwartzCommutator m B h) eta hf
  have hb := dyadicProjection_frequency W hW b
  have hball := lineSchwartzCommutator_ball m B h ((13/6)/W) (64/W)
    (fun x hx => (hb x hx).2) hh eta hc
  have hlo := (div_le_iff₀ hV).mp hd.1
  have hhi := mul_le_mul_of_nonneg_left hball hW.le
  have he : W*((13/6)/W+64/W)=(13/6:ℝ)+64 := by field_simp [hW.ne']
  rw [he] at hhi
  have hg := mul_le_mul_of_nonneg_right hWV (abs_nonneg eta)
  nlinarith

end LipschitzHilbert.PacketRepresentation

end

end OAI
