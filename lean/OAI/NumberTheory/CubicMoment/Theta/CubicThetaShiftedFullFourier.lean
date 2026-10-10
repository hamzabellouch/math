import OAI.NumberTheory.CubicMoment.Theta.CubicThetaShiftedFullObservation
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaShiftedRadialMellin

namespace OAI

/-! The full initial Fourier observation on an arbitrary positive window. -/
noncomputable section
open Set MeasureTheory
open scoped CompactlySupported
namespace CubicFirstMoment

lemma cubicThetaShiftedFullObservation_normalized (b h : Eisenstein) (W : C_c(ℝ,ℂ))
    {a : ℝ} (ha : 0<a) (d : ℝ) {K : Set CubicThetaPoint} (hK : IsCompact K)
    (hSK : cubicThetaShiftedWindow a d⊆K) {s : ℂ} (hs : 3<s.re) :
    cubicThetaShiftedFullObservation b h W a d hK s=
      cubicThetaResidueScale*((Real.pi:ℂ)/Complex.Gamma s)*
        cubicThetaShiftedFrequencyDirichlet b h s*cubicThetaShiftedWindowRadialTest h W a d s := by
  let f : ℂ×ℝ → ℂ := fun p => star (W p.2*
      (Real.fourierChar (tracePair p.1 (cubicThetaShiftedRowFrequency h)):ℂ))*
    (cubicThetaResidueScale*cubicThetaEisenstein
      (cubicThetaMobius (cubicThetaFullComplex (cubicThetaShiftedInversion b)) p) s)
  have hc : Continuous (fun p : CubicThetaPoint => cubicThetaEisenstein p.val s) := by
    apply continuous_iff_continuousAt.mpr
    intro p
    exact (cubicThetaEisenstein_continuousAt (by linarith) p.property).comp
      continuous_subtype_val.continuousAt
  have hcomp := hc.comp (continuous_const_smul (cubicThetaShiftedInversion b))
  have hf : Continuous (fun p : CubicThetaPoint =>
      star (cubicThetaShiftedFourierWeight h W p)*(cubicThetaResidueScale*
        cubicThetaEisenstein (cubicThetaShiftedInversion b • p).val s)) :=
    (cubicThetaShiftedFourierWeight_continuous h W).star.mul
    (continuous_const.mul hcomp)
  have hfc : Continuous (fun p : CubicThetaPoint => f (cubicThetaPointCoordinates p)) :=
    hf.congr (fun _ => rfl)
  have hi : IntegrableOn (fun p => f (cubicThetaPointCoordinates p))
      (cubicThetaShiftedWindow a d) cubicThetaPointMeasure :=
    (hfc.continuousOn.integrableOn_compact hK).mono_set hSK
  have hp : cubicThetaShiftedFullObservation b h W a d hK s=
      ∫ p in cubicThetaShiftedWindow a d,f (cubicThetaPointCoordinates p) ∂cubicThetaPointMeasure := by
    rw [cubicThetaShiftedFullObservation_right b h W a d hK hSK hs,←integral_const_mul]
    apply setIntegral_congr_fun (cubicThetaShiftedWindow_measurable a d)
    intro p _
    change cubicThetaResidueScale*(star (cubicThetaShiftedFourierWeight h W p)*
      cubicThetaEisenstein (cubicThetaShiftedInversion b • p).val s)=_
    dsimp only [f,cubicThetaShiftedFourierWeight,cubicThetaPointCoordinates]
    rw [cubicThetaFullPointAction_apply]
    ring
  rw [hp,cubicThetaShiftedWindow_fubini ha d f hi,cubicThetaShiftedWindowRadialTest,
    ←integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Icc
  intro v hv
  dsimp only
  have hv0 : 0<v := ha.trans_le hv.1
  calc
    _ = cubicThetaResidueScale*star (W v)/(v:ℂ)^3*
        ∫ z in cubicThetaShiftedHorizontalCell,
          star (Real.fourierChar (tracePair z (cubicThetaShiftedRowFrequency h)):ℂ)*
            cubicThetaEisenstein ((cubicThetaInversion 1 (z,v)).1+b,
              (cubicThetaInversion 1 (z,v)).2) s := by
      rw [←integral_const_mul]
      apply setIntegral_congr_fun cubicThetaShiftedHorizontalCell_measurable
      intro z _
      simp only [f,cubicThetaMobius_shiftedInversion b (p:=(z,v)) hv0,star_mul]
      ring
    _ = _ := by rw [cubicThetaShifted_horizontal_coefficient b hv0 (by linarith) h]; ring

end CubicFirstMoment

end

end OAI
