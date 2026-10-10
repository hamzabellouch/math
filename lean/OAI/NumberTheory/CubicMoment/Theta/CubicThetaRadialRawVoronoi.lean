import OAI.NumberTheory.CubicMoment.Theta.CubicThetaRadialDual
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaRawVoronoi

namespace OAI

/-! Actual radial raw/completed Voronoi identities. The main term remains
in terms of the computed residue, without asserting its normalization. -/
noncomputable section
open scoped BigOperators ContDiff
namespace CubicFirstMoment

def cubicThetaActualRawRadialMain (r : Eisenstein) (W : ℝ→ℂ) (X : ℝ) : ℂ :=
  cubicThetaResidueRadialPole r/
    (((3^(5/2:ℝ):ℝ):ℂ)*((Real.sqrt (norm r):ℂ)*gauss r))*
      mellin W (5/6)*((X/27:ℝ):ℂ)^(5/6:ℂ)

def cubicThetaActualCompletedRadialMain (r : Eisenstein) (W : ℝ→ℂ) (X : ℝ) : ℂ :=
  cubicThetaResidueRadialPole r/
    (((3^(5/2:ℝ):ℝ):ℂ)*(Real.sqrt (norm r):ℂ))*
      mellin W (5/6)*((X/27:ℝ):ℂ)^(5/6:ℂ)

lemma cubicThetaRadialGauss_ne_zero {r : Eisenstein} (hr : primary r) (hs : Squarefree r) :
    gauss r≠0 := by
  apply norm_ne_zero_iff.mp
  rw [norm_gauss_of_squarefree hr hs]
  norm_num

lemma cubicThetaRadialRawScalar_ne_zero {r : Eisenstein} (hr : primary r) (hs : Squarefree r) :
    (((3^(5/2:ℝ):ℝ):ℂ)*((Real.sqrt (norm r):ℂ)*gauss r))≠0 := by
  apply mul_ne_zero
  · exact Complex.ofReal_ne_zero.mpr (Real.rpow_pos_of_pos (by norm_num) _).ne'
  · exact mul_ne_zero (Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr
      (norm_pos_of_ne_zero (primary_ne_zero hr))).ne') (cubicThetaRadialGauss_ne_zero hr hs)

theorem cubicTheta_raw_radial_voronoi {r : Eisenstein} (hr : primary r) (hs : Squarefree r)
    [Fintype (Residues r)] (W : ℝ→ℂ) (hW : HasCompactSupport W)
    (hpos : tsupport W⊆Set.Ioi 0) (hsm : ContDiff ℝ ∞ W)
    {σ X : ℝ} (hσ : 0<σ) (hX : 0<X) :
    Summable (metaplecticDualTerm cubicThetaCoreCoefficient r 0 W σ (X/729)) ∧
    metaplecticRawCompleted r 0 W X=
      81*metaplecticRawPrefactor r 0*
        ∑' nd,metaplecticDualTerm cubicThetaCoreCoefficient r 0 W σ (X/729) nd+
      cubicThetaActualRawRadialMain r W X := by
  obtain ⟨hS,hE⟩ := cubicThetaFullDual_radial_voronoi hr hs W hW hpos hsm hσ hX
  refine ⟨hS,?_⟩
  let A := ((3^(5/2:ℝ):ℝ):ℂ)*((Real.sqrt (norm r):ℂ)*gauss r)
  have hA : A≠0 := cubicThetaRadialRawScalar_ne_zero hr hs
  have hscalar : A*(81*metaplecticRawPrefactor r 0)=cubicThetaDualPrefactor r*27 := by
    simpa only [A,cubicThetaCircleOrder,Bool.not_false,Bool.false_eq_true,ite_true,ite_false,
      Nat.cast_zero,neg_zero,theta_zero,mul_one,cubicThetaLevelAngularRoot,pow_zero,
      inv_one,one_mul] using cubicThetaDual_scalar hr hs false 0
  have hp : A*cubicThetaActualRawRadialMain r W X=
      cubicThetaResidueRadialPole r*mellin W (5/6)*((X/27:ℝ):ℂ)^(5/6:ℂ) := by
    change A*(cubicThetaResidueRadialPole r/A*mellin W (5/6)*((X/27:ℝ):ℂ)^(5/6:ℂ))=_
    field_simp
  apply mul_left_cancel₀ hA
  rw [mul_add,←mul_assoc,hscalar,hp]
  exact hE

lemma cubicTheta_radial_main_completed {r : Eisenstein} (hr : primary r) (hs : Squarefree r)
    (W : ℝ→ℂ) (X : ℝ) :
    gauss r*cubicThetaActualRawRadialMain r W X=cubicThetaActualCompletedRadialMain r W X := by
  have hg := cubicThetaRadialGauss_ne_zero hr hs
  have hthree : ((3^(5/2:ℝ):ℝ):ℂ)≠0 :=
    Complex.ofReal_ne_zero.mpr (Real.rpow_pos_of_pos (by norm_num) _).ne'
  have hsqrt : (Real.sqrt (norm r):ℂ)≠0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (norm_pos_of_ne_zero (primary_ne_zero hr))).ne'
  unfold cubicThetaActualRawRadialMain cubicThetaActualCompletedRadialMain
  field_simp

theorem cubicTheta_completed_radial_voronoi {r : Eisenstein} (hr : primary r) (hs : Squarefree r)
    (W : ℝ→ℂ) (hW : HasCompactSupport W) (hpos : tsupport W⊆Set.Ioi 0)
    (hsm : ContDiff ℝ ∞ W) {σ X : ℝ} (hσ : 0<σ) (hX : 0<X) :
    metaplecticCompleted r 0 W X=
      81*metaplecticPrefactor r 0*
        ∑' nd,metaplecticDualTerm cubicThetaCoreCoefficient r 0 W σ (X/729) nd+
      cubicThetaActualCompletedRadialMain r W X := by
  let : Finite (Residues r) := finite_residues (primary_ne_zero hr)
  let : Fintype (Residues r) := Fintype.ofFinite _
  rw [metaplecticCompleted_eq_raw hr,(cubicTheta_raw_radial_voronoi hr hs W hW hpos hsm hσ hX).2,
    theta_zero,mul_one,mul_add,cubicTheta_radial_main_completed hr hs]
  congr 1
  calc
    _ = 81*(gauss r*theta 0 r*metaplecticRawPrefactor r 0)*
        ∑' nd,metaplecticDualTerm cubicThetaCoreCoefficient r 0 W σ (X/729) nd := by rw [theta_zero]; ring
    _ = _ := by rw [metaplecticPrefactor_normalization hr hs]

end CubicFirstMoment

end

end OAI
