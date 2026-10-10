import OAI.Analysis.LipschitzHilbert.Trees.SourceBoxReproduction

namespace OAI

/-! A pointwise-a.e. comparison on a full rectangle gives its normalized
integral comparison, with the actual product-Lebesgue area. -/
noncomputable section
open Set MeasureTheory
namespace LipschitzHilbert

theorem coordinateBox_eq_prod (a b r W : ℝ) :
    coordinateBox a b r W=Icc (a-r) (a+r) ×ˢ Icc (b-W) (b+W) := by
  ext z
  simp only [coordinateBox,mem_ofPred_eq,mem_prod,mem_Icc,abs_le]
  constructor <;> rintro ⟨⟨h1,h2⟩,⟨h3,h4⟩⟩ <;> constructor <;> constructor <;> linarith

theorem coordinateBox_measure (a b r W : ℝ) (hr : 0≤r) (hW : 0≤W) :
    (volume.prod volume).real (coordinateBox a b r W)=4*r*W := by
  rw [coordinateBox_eq_prod,measureReal_prod_prod,
    Real.volume_real_Icc_of_le (by linarith),Real.volume_real_Icc_of_le (by linarith)]
  ring

theorem coordinateBox_measure_ne_top (a b r W : ℝ) :
    (volume.prod volume) (coordinateBox a b r W)≠⊤ := by
  simp only [coordinateBox_eq_prod,Measure.prod_prod,Real.volume_Icc]
  exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top

theorem integral_comparison_on_box (a b r W I C : ℝ) (hr : 0<r) (hW : 0<W)
    (F : ℝ×ℝ → ℝ) (hF : IntegrableOn F (coordinateBox a b r W) (volume.prod volume))
    (hpoint : ∀ᵐ z ∂volume.prod volume, z∈coordinateBox a b r W → I≤C*(r*W)*F z) :
    I≤(C/4)*∫ z in coordinateBox a b r W, F z ∂volume.prod volume := by
  let box := coordinateBox a b r W
  have hbox := coordinateBox_measurable a b r W
  let : IsFiniteMeasure ((volume.prod volume).restrict box) :=
    isFiniteMeasure_restrict.mpr (coordinateBox_measure_ne_top a b r W)
  have hbound : (∫ _z in box, I ∂volume.prod volume)≤
      ∫ z in box, C*(r*W)*F z ∂volume.prod volume := by
    apply integral_mono_ae (integrable_const I) (hF.const_mul _)
    exact (ae_restrict_iff' hbox).mpr hpoint
  rw [integral_const,measureReal_restrict_apply_univ,smul_eq_mul,integral_const_mul] at hbound
  change (volume.prod volume).real (coordinateBox a b r W)*I≤
    C*(r*W)*(∫ z in coordinateBox a b r W, F z ∂volume.prod volume) at hbound
  rw [coordinateBox_measure a b r W hr.le hW.le] at hbound
  apply (mul_le_mul_iff_left₀ (mul_pos (by norm_num : (0:ℝ)<4) (mul_pos hr hW))).mp
  convert hbound using 1 <;> ring

end LipschitzHilbert

end

end OAI
