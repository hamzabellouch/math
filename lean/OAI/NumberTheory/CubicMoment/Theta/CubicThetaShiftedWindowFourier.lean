import OAI.NumberTheory.CubicMoment.Theta.CubicThetaShiftedWindowTest

namespace OAI

/-! The exact initial Fourier observation on a finite translated-cusp window. -/
noncomputable section
open Set MeasureTheory
open scoped CompactlySupported
namespace CubicFirstMoment

def cubicThetaShiftedWindowRadialTest (h : Eisenstein) (W : C_c(ℝ,ℂ))
    (a d : ℝ) (s : ℂ) : ℂ :=
  ∫ v in Icc a d,star (W v)*(v:ℂ)^s*
    (∫ t in Ioi (0:ℝ),cubicThetaDualHeat v s (cubicThetaShiftedRowHeatScale h) t)/(v:ℂ)^3

lemma cubicThetaShiftedWindowObservation_normalized (b h : Eisenstein) (W : C_c(ℝ,ℂ))
    {a : ℝ} (ha : 0<a) (d : ℝ) {K : Set CubicThetaPoint} (hK : IsCompact K)
    (hSK : cubicThetaShiftedWindow a d⊆K) (hhigh : ∀ p∈K,1<p.val.2)
    {s : ℂ} (hs : 3<s.re) :
    cubicThetaShiftedWindowObservation b h W a d hK s=
      cubicThetaResidueScale*((Real.pi:ℂ)/Complex.Gamma s)*
        cubicThetaShiftedFrequencyDirichlet b h s*cubicThetaShiftedWindowRadialTest h W a d s := by
  let f : ℂ×ℝ → ℂ := fun p => star (W p.2*
      (Real.fourierChar (tracePair p.1 (cubicThetaShiftedRowFrequency h)):ℂ))*
    (cubicThetaResidueScale*cubicThetaEisenstein
      ((cubicThetaInversion 1 p).1+b,(cubicThetaInversion 1 p).2) s)
  have hi : IntegrableOn (fun p => f (cubicThetaPointCoordinates p))
      (cubicThetaShiftedWindow a d) cubicThetaPointMeasure :=
    cubicThetaShiftedWindowTest_integrable h W a d hK hSK _ _
      (cubicThetaCompactShiftedFamily_right b hK hhigh hs)
  have hp : cubicThetaShiftedWindowObservation b h W a d hK s=
      ∫ p in cubicThetaShiftedWindow a d,f (cubicThetaPointCoordinates p) ∂cubicThetaPointMeasure :=
    cubicThetaShiftedWindowTest_pairing h W a d hK hSK _ _
      (cubicThetaCompactShiftedFamily_right b hK hhigh hs)
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
      simp only [f,star_mul]
      ring
    _ = _ := by rw [cubicThetaShifted_horizontal_coefficient b hv0 (by linarith) h]; ring

end CubicFirstMoment

end

end OAI
