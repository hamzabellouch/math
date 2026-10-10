import OAI.NumberTheory.CubicMoment.Theta.CubicThetaRadialAverage
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaDualIndex
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaDualScalar

namespace OAI

/-! The radial dual sum uses the same proved local support and free-cube
reindexing as the angular formula. Its separate actual pole is retained. -/
noncomputable section
open scoped BigOperators ContDiff
namespace CubicFirstMoment

theorem cubicThetaFullDual_radial_voronoi {r : Eisenstein} (hr : primary r) (hs : Squarefree r)
    [Fintype (Residues r)] (W : ℝ→ℂ) (hW : HasCompactSupport W)
    (hpos : tsupport W⊆Set.Ioi 0) (hsm : ContDiff ℝ ∞ W)
    {σ X : ℝ} (hσ : 0<σ) (hX : 0<X) :
    Summable (metaplecticDualTerm cubicThetaCoreCoefficient r 0 W σ (X/729)) ∧
    (((3^(5/2:ℝ):ℝ):ℂ)*((Real.sqrt (norm r):ℂ)*gauss r))*
      metaplecticRawCompleted r 0 W X=
      (cubicThetaDualPrefactor r*27)*
        ∑' nd,metaplecticDualTerm cubicThetaCoreCoefficient r 0 W σ (X/729) nd+
      cubicThetaResidueRadialPole r*mellin W (5/6)*((X/27:ℝ):ℂ)^(5/6:ℂ) := by
  obtain ⟨hS,hE⟩ := cubicThetaResidue_radial_voronoi hr hs W hW hpos hsm hσ hX
  rw [cubicThetaResidueDualTerm_local hr hs] at hS hE
  have hI := hS.comp_injective cubicThetaCommonArgument_injective
  have hJ := hI.comp_injective (cubicThetaFreeCubeJoin_injective (primary_ne_zero hr))
  have he := cubicThetaFreeLocalDualTerm_eq hr false 0 W σ X
  have hfree := hJ.congr he
  rw [cubicThetaLocalDualTerm_reindex,cubicTheta_free_cube_tsum (primary_ne_zero hr)] at hE
  simp only [he] at hE
  have hf (x : CubicThetaCoreIndex r × CubicThetaFreeArgument r) :
      cubicThetaFreeLocalDualTerm r false 0 W σ X x=
        27*metaplecticDualTerm cubicThetaCoreCoefficient r 0 W σ (X/729)
          (cubicThetaCoreFreeArgument r x) := by
    simpa only [cubicThetaCircleOrder,Bool.not_false,Bool.false_eq_true,ite_true,ite_false,
      Nat.cast_zero,neg_zero,theta_zero,mul_one] using
      cubicThetaFreeLocalDualTerm_frequency hr false 0 W σ X x
  have hprod := hfree.congr hf
  have hsmall := (summable_mul_left_iff (by norm_num : (27:ℂ)≠0)).mp hprod
  refine ⟨(cubicThetaDualTerm_summable_iff r 0 W σ (X/729)).mp hsmall,?_⟩
  simp only [hf,tsum_mul_left,cubicThetaDualTerm_tsum,mul_assoc] at hE
  simpa only [mul_assoc] using hE

end CubicFirstMoment

end

end OAI
