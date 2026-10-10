import OAI.NumberTheory.CubicMoment.Theta.CubicThetaTorusCellTransport

namespace OAI

/-! The actual horizontal characters separate square-integrable functions
on the half-open arithmetic cell. No periodic representative is assumed. -/
noncomputable section
open MeasureTheory Set
namespace CubicFirstMoment
local instance cubicThetaCellFourierSeparationMeasureSpace : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩

lemma cubicThetaCellFourier_coefficient {f : ℂ → ℂ}
    (hf : MemLp f 2 ((volume : Measure ℂ).restrict cubicThetaHorizontalCell))
    (h : Eisenstein) :
    cubicThetaTorusCoefficient ((cubicThetaTorusCellPoint_memLp hf).toLp _) h=
      (2/(9*Real.sqrt 3):ℝ) •
        ∫ z in cubicThetaHorizontalCell,
          star (Real.fourierChar (tracePair z (cubicThetaRowFrequency h)):ℂ)*f z := by
  unfold cubicThetaTorusCoefficient UnitAddTorus.mFourierCoeff
  simp only [UnitAddTorus.mFourier_neg,starRingEnd_apply,smul_eq_mul]
  calc
    _ = ∫ u : UnitAddTorus (Fin 2),star (cubicThetaTorusFourier h u)*
        f (cubicThetaTorusCellPoint u) := by
      apply integral_congr_ae
      filter_upwards [(cubicThetaTorusCellPoint_memLp hf).coeFn_toLp] with u hu
      rw [hu]
      rfl
    _ = _ := by
      simp_rw [cubicThetaTorusCellPoint_character]
      exact cubicThetaTorusCellPoint_integral (fun z =>
        star (Real.fourierChar (tracePair z (cubicThetaRowFrequency h)):ℂ)*f z)

theorem cubicThetaCellFourier_separates {f : ℂ → ℂ}
    (hf : MemLp f 2 ((volume : Measure ℂ).restrict cubicThetaHorizontalCell))
    (hzero : ∀ h : Eisenstein,
      (∫ z in cubicThetaHorizontalCell,
        star (Real.fourierChar (tracePair z (cubicThetaRowFrequency h)):ℂ)*f z)=0) :
    f =ᵐ[(volume : Measure ℂ).restrict cubicThetaHorizontalCell] 0 := by
  let F : CubicThetaTorusL2 := (cubicThetaTorusCellPoint_memLp hf).toLp _
  have hc (h : Eisenstein) : cubicThetaTorusCoefficient F h=0 := by
    rw [cubicThetaCellFourier_coefficient hf,hzero h,smul_zero]
  have hn : ‖F‖^2=0 := by
    rw [←cubicThetaTorus_parseval]
    simp only [hc,norm_zero,zero_pow (by decide : 2≠0),tsum_zero]
  have hF : F=0 := norm_eq_zero.mp (sq_eq_zero_iff.mp hn)
  have hφ : (f ∘ cubicThetaTorusCellPoint) =ᵐ[volume] 0 :=
    (cubicThetaTorusCellPoint_memLp hf).coeFn_toLp.symm.trans
      (Lp.eq_zero_iff_ae_eq_zero.mp hF)
  have hm : f =ᵐ[Measure.map cubicThetaTorusCellPoint volume] 0 :=
    cubicThetaTorusCellPoint_embedding.ae_map_iff.mpr hφ
  rw [cubicThetaTorusCellPoint_map] at hm
  exact (Measure.ae_ennreal_smul_measure_iff (by positivity :
    ENNReal.ofReal (2/(9*Real.sqrt 3))≠0)).mp hm

end CubicFirstMoment

end

end OAI
