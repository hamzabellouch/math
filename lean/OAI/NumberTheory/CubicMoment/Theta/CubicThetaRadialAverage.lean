import OAI.NumberTheory.CubicMoment.Theta.CubicThetaRadialVoronoi
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaRadialResidue
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaAveragedVoronoi

namespace OAI

/-! Finite cubic-character averaging of the actual radial formula. The
pole coefficient is calculated without assuming the arithmetic scalar. -/
noncomputable section
open scoped BigOperators MatrixGroups ContDiff
namespace CubicFirstMoment

def cubicThetaResidueRadialPole (r : Eisenstein) : ℂ :=
  cubicThetaAngularUncompletion r 0 (5/6)/2*
    ((Nat.card (Residues r)ˣ:ℂ)*(star cubicThetaSeriesConstant/3))*
      ((cubicThetaLevelScale r^(2/3:ℝ):ℝ):ℂ)

lemma cubicThetaResidueRadialPole_sum (r : Eisenstein) (hr : primary r)
    [Fintype (Residues r)] :
    (∑ u : Residues r,cubicSymbol r (residueRepresentative r u)*
      cubicThetaSelectedRadialResidue (cubicThetaResidueCuspMatrix r hr (residueRepresentative r u))
        (cubicThetaResidueCuspPrimary r hr (residueRepresentative r u)))=
      cubicThetaResidueRadialPole r := by
  simp only [cubicThetaSelectedRadialResidue,cubicThetaResidueCuspMatrix_bottom]
  calc
    _ = cubicThetaAngularUncompletion r 0 (5/6)/2*
        (∑ u : Residues r,cubicSymbol r (residueRepresentative r u)*
          cubicThetaProjectedRadialConstant
            (cubicThetaResidueCuspMatrix r hr (residueRepresentative r u))
            (cubicThetaResidueCuspPrimary r hr (residueRepresentative r u))) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro u _
      ring
    _ = _ := by
      rw [cubicThetaResidueRadialConstant,cubicThetaResidueConstant_units]
      dsimp [cubicThetaResidueRadialPole]
      ring

theorem cubicThetaResidue_radial_voronoi {r : Eisenstein} (hr : primary r) (hs : Squarefree r)
    [Fintype (Residues r)] (W : ℝ→ℂ) (hW : HasCompactSupport W)
    (hpos : tsupport W⊆Set.Ioi 0) (hsm : ContDiff ℝ ∞ W)
    {σ X : ℝ} (hσ : 0<σ) (hX : 0<X) :
    Summable (cubicThetaResidueDualTerm r hr false 0 W σ X) ∧
    (((3^(5/2:ℝ):ℝ):ℂ)*((Real.sqrt (norm r):ℂ)*gauss r))*
      metaplecticRawCompleted r 0 W X=
      cubicThetaDualPrefactor r*∑' n,cubicThetaResidueDualTerm r hr false 0 W σ X n+
        cubicThetaResidueRadialPole r*mellin W (5/6)*((X/27:ℝ):ℂ)^(5/6:ℂ) := by
  let g (u : Residues r) := cubicThetaResidueCuspMatrix r hr (residueRepresentative r u)
  let hp (u : Residues r) := cubicThetaResidueCuspPrimary r hr (residueRepresentative r u)
  let w (u : Residues r) := cubicSymbol r (residueRepresentative r u)
  let D (u : Residues r) (n : MetaplecticDualArgument) : ℂ :=
    cubicThetaCoefficientTwist (cubicThetaProjectedCoefficient (g u) (hp u))
      (cubicThetaPrimaryDualCenter (g u)) n.val/(‖cubicThetaFrequency n.val‖:ℂ)*
      metaplecticTransform 0 W σ
        (cubicThetaDualScale r (X/27)*‖cubicThetaFrequency n.val‖^2)
  let M := mellin W (5/6)*((X/27:ℝ):ℂ)^(5/6:ℂ)
  have hE (u : Residues r) : Summable (D u) ∧
      cubicThetaSelectedAdditiveSum (g u) false 0 W (X/27)=
        cubicThetaDualPrefactor r*∑' n,D u n+cubicThetaSelectedRadialResidue (g u) (hp u)*M := by
    have H := cubicThetaSelected_radial_voronoi (g u) (hp u) W hW hpos hsm hσ
      (div_pos hX (by norm_num) : 0<X/27)
    simpa only [g,cubicThetaResidueCuspMatrix_bottom,D,M,mul_assoc] using H
  have ht (n : MetaplecticDualArgument) :
      (∑ u : Residues r,w u*D u n)=cubicThetaResidueDualTerm r hr false 0 W σ X n := by
    unfold cubicThetaResidueDualTerm cubicThetaResidueDualCoefficient
    simp only [cubicThetaCircleOrder,Bool.false_eq_true,ite_false,Bool.not_false,ite_true,
      Nat.cast_zero,neg_zero,theta_zero,one_mul,Finset.sum_div,Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro u _
    dsimp only [w,D,g,hp]
    ring
  have hsum : Summable (fun n : MetaplecticDualArgument => ∑ u : Residues r,w u*D u n) :=
    summable_sum (fun u _ => (hE u).1.mul_left (w u))
  refine ⟨hsum.congr ht,?_⟩
  have hl := cubicThetaSelectedSmoothSum_average_raw hr hs 0 W hW hX
  have hl' : (∑ u : Residues r,w u*cubicThetaSelectedAdditiveSum (g u) false 0 W (X/27))=
      (((3^(5/2:ℝ):ℝ):ℂ)*((Real.sqrt (norm r):ℂ)*gauss r))*
        metaplecticRawCompleted r 0 W X := by
    simpa only [g,w,cubicThetaResidueCuspMatrix_weighted,theta_zero,mul_one,
      cubicThetaCircleOrder,Bool.not_false,ite_true,Nat.cast_zero,neg_zero] using hl
  rw [←hl']
  calc
    _ = cubicThetaDualPrefactor r*(∑ u : Residues r,∑' n,w u*D u n)+
        (∑ u : Residues r,w u*cubicThetaSelectedRadialResidue (g u) (hp u))*M := by
      simp_rw [(hE _).2,mul_add,Finset.sum_add_distrib,Finset.mul_sum,Finset.sum_mul]
      congr 1
      · apply Finset.sum_congr rfl
        intro u _
        rw [tsum_mul_left]
        ring
      · apply Finset.sum_congr rfl
        intro u _
        ring
    _ = cubicThetaDualPrefactor r*(∑' n,∑ u : Residues r,w u*D u n)+
        cubicThetaResidueRadialPole r*M := by
      rw [Summable.tsum_finsetSum (fun u _ => (hE u).1.mul_left (w u))]
      rw [show (∑ u : Residues r,w u*cubicThetaSelectedRadialResidue (g u) (hp u))=
        cubicThetaResidueRadialPole r from cubicThetaResidueRadialPole_sum r hr]
    _ = _ := by simp_rw [ht]; dsimp [M]; ring

end CubicFirstMoment

end

end OAI
