import OAI.NumberTheory.CubicMoment.Theta.CubicThetaHighHeatNonzero
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaRadialMellinIdentity
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff

namespace OAI

/-! Compact radial tests separate the Fourier heat kernel at every
parameter in Re(s)>1. The test may depend on the parameter. -/
noncomputable section
open Set Filter MeasureTheory Topology
open scoped CompactlySupported
namespace CubicFirstMoment

theorem cubicThetaComplexRadialTest_nonzero {h : Eisenstein} (hh : h≠0)
    {s : ℂ} (hs : 1<s.re) :
    ∃ W : C_c(ℝ,ℂ), (∀ v≤(2:ℝ), W v=0) ∧ cubicThetaFourierRadialTest h W s≠0 := by
  let A := cubicThetaRowHeatScale h
  have hA : 0<A := cubicThetaRowHeatScale_pos hh
  let F (v : ℝ) := cubicThetaComplexHeightIntegral s A (v:ℂ)/(v:ℂ)^2
  have hc : ContinuousOn F (Ioi (2:ℝ)) := by
    intro v hv
    have hp : 0<v := by have := hv; change 2<v at this; linarith
    have hk := (cubicThetaComplexHeightIntegral_analytic s hA (z:=(v:ℂ)) (by simpa)).continuousAt
    exact ((hk.comp Complex.continuous_ofReal.continuousAt).div
      (Complex.continuous_ofReal.continuousAt.pow 2)
      (pow_ne_zero 2 (Complex.ofReal_ne_zero.mpr hp.ne'))).continuousWithinAt
  obtain ⟨v,hv,hn⟩ := cubicThetaHighHeat_nonzero hs hA
  have hFn : F v≠0 := div_ne_zero
    (mt (cubicThetaComplexHeightIntegral_real_zero_iff s A (by linarith)).mp hn)
    (pow_ne_zero 2 (Complex.ofReal_ne_zero.mpr (by linarith : v≠0)))
  by_contra hnone
  push Not at hnone
  have hae := isOpen_Ioi.ae_eq_zero_of_integral_contDiff_smul_eq_zero
    (hc.locallyIntegrableOn measurableSet_Ioi) (fun g hg hgc hgu => by
      let W : C_c(ℝ,ℂ) := {
        toFun := fun v => (g v:ℂ)
        continuous_toFun := Complex.continuous_ofReal.comp hg.continuous
        hasCompactSupport' := hgc.comp_left (g:=fun r : ℝ => (r:ℂ)) (by simp) }
      have hW : ∀ v≤(2:ℝ), W v=0 := by
        intro v hv
        have hz : g v=0 := image_eq_zero_of_notMem_tsupport (fun ht => (not_lt_of_ge hv) (hgu ht))
        change (g v:ℂ)=0
        rw [hz,Complex.ofReal_zero]
      have he : (∫ v : ℝ, g v • F v)=cubicThetaFourierRadialTest h W s := by
        rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s:=Ioi (2:ℝ)) (fun v hv => by
          have hz : g v=0 := image_eq_zero_of_notMem_tsupport (fun ht => hv (hgu ht))
          rw [hz,zero_smul])]
        rw [cubicThetaFourierRadialTest_dilated]
        apply setIntegral_congr_fun measurableSet_Ioi
        intro v _
        dsimp only [F]
        rw [cubicThetaComplexHeightIntegral_real]
        change (g v:ℂ)*((∫ u in Ioi (0:ℝ), (u:ℂ)^(s-2)*cubicThetaLinearHeat v A u)/(v:ℂ)^2)=
          star (g v:ℂ)/(v:ℂ)^2*(∫ u in Ioi (0:ℝ), (u:ℂ)^(s-2)*cubicThetaLinearHeat v A u)
        simp only [Complex.star_def,Complex.conj_ofReal]
        ring
      exact he.trans (hnone W hW))
  have hae' : F=ᵐ[volume.restrict (Ioi (2:ℝ))] 0 := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi,ae_restrict_of_ae hae] with t ht he
    exact he ht
  have he := Measure.eqOn_open_of_ae_eq hae' isOpen_Ioi hc continuousOn_const
  exact hFn (he hv)

end CubicFirstMoment

end

end OAI
