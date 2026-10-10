import OAI.NumberTheory.CubicMoment.Theta.CubicThetaCellFourierSeparation
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaHorizontalDomain

namespace OAI

/-! Actual periodic continuous functions are determined by their cell coefficients. -/
noncomputable section
open Set MeasureTheory Filter
namespace CubicFirstMoment
local instance : Countable Eisenstein := cubicThetaFourierIndex.injective.countable

theorem cubicThetaContinuousFourier_ext {f g : ℂ → ℂ} (hf : Continuous f) (hg : Continuous g)
    (hfp : ∀ (m : Eisenstein) z,f (z+3*(m:ℂ))=f z)
    (hgp : ∀ (m : Eisenstein) z,g (z+3*(m:ℂ))=g z)
    (he : ∀ h : Eisenstein,
      (∫ z in cubicThetaHorizontalCell,
        star (Real.fourierChar (tracePair z (cubicThetaRowFrequency h)):ℂ)*f z)=
      ∫ z in cubicThetaHorizontalCell,
        star (Real.fourierChar (tracePair z (cubicThetaRowFrequency h)):ℂ)*g z) : f=g := by
  obtain ⟨L,hL,hcell⟩ := cubicThetaHorizontalCell_compact_container
  let : IsFiniteMeasure ((volume : Measure ℂ).restrict cubicThetaHorizontalCell) :=
    isFiniteMeasure_restrict.mpr cubicThetaHorizontalCell_measure_ne_top
  have hD : MemLp (fun z => f z-g z) 2
      ((volume : Measure ℂ).restrict cubicThetaHorizontalCell) := by
    obtain ⟨C,hC⟩ := hL.exists_bound_of_continuousOn (hf.sub hg).continuousOn
    apply MemLp.of_bound (hf.sub hg).aestronglyMeasurable C
    filter_upwards [ae_restrict_mem cubicThetaHorizontalCell_measurable] with z hz
    exact hC z (hcell hz)
  have hphase (h : Eisenstein) : Continuous (fun z : ℂ =>
      star (Real.fourierChar (tracePair z (cubicThetaRowFrequency h)):ℂ)) := by
    have hc : Continuous (fun z : ℂ => Real.fourierChar (tracePair z (cubicThetaRowFrequency h))) :=
      Real.continuous_fourierChar.comp (by unfold tracePair; fun_prop)
    exact (continuous_subtype_val.comp hc).star
  have hi (h : Eisenstein) (F : ℂ → ℂ) (hF : Continuous F) :
      IntegrableOn (fun z => star (Real.fourierChar
        (tracePair z (cubicThetaRowFrequency h)):ℂ)*F z) cubicThetaHorizontalCell :=
    (((hphase h).mul hF).continuousOn.integrableOn_compact hL).mono_set hcell
  have hcellzero := cubicThetaCellFourier_separates hD (fun h => by
    simp_rw [mul_sub]
    rw [integral_sub (hi h f hf) (hi h g hg),he h,sub_self])
  have hcell' : ∀ᵐ z ∂(volume : Measure ℂ),z∈cubicThetaHorizontalCell → f z=g z := by
    have ht := (ae_restrict_iff' cubicThetaHorizontalCell_measurable).mp hcellzero
    filter_upwards [ht] with z hz hmem
    exact sub_eq_zero.mp (hz hmem)
  have htrans : ∀ᵐ z ∂(volume : Measure ℂ),∀ m : Eisenstein,
      z+3*(m:ℂ)∈cubicThetaHorizontalCell → f z=g z := by
    apply ae_all_iff.mpr
    intro m
    have ht := (measurePreserving_add_right volume (3*(m:ℂ))).quasiMeasurePreserving.ae hcell'
    filter_upwards [ht] with z hz hmem
    simpa only [hfp m z,hgp m z] using hz hmem
  have hall : f=ᵐ[(volume : Measure ℂ)] g := by
    filter_upwards [htrans] with z hz
    obtain ⟨m,hm,_⟩ := cubicThetaHorizontalCell_unique z
    exact hz (Multiplicative.toAdd m) hm
  exact Measure.eq_of_ae_eq hall hf hg

end CubicFirstMoment

end

end OAI
