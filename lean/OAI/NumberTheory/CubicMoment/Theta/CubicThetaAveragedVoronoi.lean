import OAI.NumberTheory.CubicMoment.Theta.CubicThetaResidueCusps
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaRawPairs

namespace OAI

/-! A concrete finite character average of the proved angular additive
Voronoi formula. The coefficient is the actual finite cusp average; further
local/Moebius simplification is kept separate. -/
noncomputable section
open scoped BigOperators MatrixGroups ContDiff
namespace CubicFirstMoment

def cubicThetaResidueDualCoefficient (r : Eisenstein) (hr : primary r)
    [Fintype (Residues r)] (n : Eisenstein) : ℂ :=
  ∑ u : Residues r,cubicSymbol r (residueRepresentative r u)*
    cubicThetaCoefficientTwist
      (cubicThetaProjectedCoefficient (cubicThetaResidueCuspMatrix r hr (residueRepresentative r u))
        (cubicThetaResidueCuspPrimary r hr (residueRepresentative r u)))
      (cubicThetaPrimaryDualCenter (cubicThetaResidueCuspMatrix r hr (residueRepresentative r u))) n

def cubicThetaResidueDualTerm (r : Eisenstein) (hr : primary r) [Fintype (Residues r)]
    (rev : Bool) (k : ℕ) (W : ℝ→ℂ) (σ X : ℝ) (n : MetaplecticDualArgument) : ℂ :=
  theta (cubicThetaCircleOrder rev k) n.val*cubicThetaResidueDualCoefficient r hr n.val/
    (‖cubicThetaFrequency n.val‖:ℂ)*
      metaplecticTransform (cubicThetaCircleOrder (!rev) k) W σ
        (cubicThetaDualScale r (X/27)*‖cubicThetaFrequency n.val‖^2)

theorem cubicThetaResidue_voronoi {r : Eisenstein} (hr : primary r) (hs : Squarefree r)
    [Fintype (Residues r)] (rev : Bool) {k : ℕ} (hk : 0<k)
    (W : ℝ→ℂ) (hW : HasCompactSupport W) (hpos : tsupport W ⊆ Set.Ioi 0)
    (hsm : ContDiff ℝ ∞ W) {σ X : ℝ} (hσ : 0<σ) (hX : 0<X) :
    Summable (cubicThetaResidueDualTerm r hr rev k W σ X) ∧
    ((((3^(5/2:ℝ):ℝ):ℂ)*theta (cubicThetaCircleOrder (!rev) k) lambdaE)*
      ((Real.sqrt (norm r):ℂ)*gauss r))*
        metaplecticRawCompleted r (cubicThetaCircleOrder (!rev) k) W X=
    (cubicThetaLevelAngularRoot r rev k)⁻¹*cubicThetaDualPrefactor r*
      ∑' n,cubicThetaResidueDualTerm r hr rev k W σ X n := by
  let g (u : Residues r) := cubicThetaResidueCuspMatrix r hr (residueRepresentative r u)
  let hp (u : Residues r) := cubicThetaResidueCuspPrimary r hr (residueRepresentative r u)
  let w (u : Residues r) := cubicSymbol r (residueRepresentative r u)
  let D (u : Residues r) (n : MetaplecticDualArgument) : ℂ :=
    theta (cubicThetaCircleOrder rev k) n.val*
      cubicThetaCoefficientTwist (cubicThetaProjectedCoefficient (g u) (hp u))
        (cubicThetaPrimaryDualCenter (g u)) n.val/(‖cubicThetaFrequency n.val‖:ℂ)*
      metaplecticTransform (cubicThetaCircleOrder (!rev) k) W σ
        (cubicThetaDualScale r (X/27)*‖cubicThetaFrequency n.val‖^2)
  let P := (cubicThetaLevelAngularRoot r rev k)⁻¹*cubicThetaDualPrefactor r
  have hE (u : Residues r) : Summable (D u) ∧
      cubicThetaSelectedAdditiveSum (g u) rev k W (X/27)=P*∑' n,D u n := by
    have H := cubicThetaSelected_voronoi (g u) (hp u) rev hk W hW hpos hsm hσ
      (div_pos hX (by norm_num) : 0<X/27)
    simpa only [g,cubicThetaResidueCuspMatrix_bottom,D,P] using H
  have ht (n : MetaplecticDualArgument) :
      (∑ u : Residues r,w u*D u n)=cubicThetaResidueDualTerm r hr rev k W σ X n := by
    unfold cubicThetaResidueDualTerm cubicThetaResidueDualCoefficient
    simp only [Finset.mul_sum,Finset.sum_div,Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro u _
    dsimp only [w,D,g,hp]
    ring
  have hsum : Summable (fun n : MetaplecticDualArgument => ∑ u : Residues r,w u*D u n) :=
    summable_sum (fun u _ => (hE u).1.mul_left (w u))
  refine ⟨hsum.congr ht,?_⟩
  have hl := cubicThetaSelectedSmoothSum_average_raw hr hs (cubicThetaCircleOrder (!rev) k) W hW hX
  have hl' : (∑ u : Residues r,w u*cubicThetaSelectedAdditiveSum (g u) rev k W (X/27))=
      ((((3^(5/2:ℝ):ℝ):ℂ)*theta (cubicThetaCircleOrder (!rev) k) lambdaE)*
        ((Real.sqrt (norm r):ℂ)*gauss r))*
          metaplecticRawCompleted r (cubicThetaCircleOrder (!rev) k) W X := by
    simpa only [g,w,cubicThetaResidueCuspMatrix_weighted] using hl
  rw [←hl']
  change _=P*∑' n,cubicThetaResidueDualTerm r hr rev k W σ X n
  calc
    _ = P*∑ u : Residues r,∑' n,w u*D u n := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro u _
      rw [(hE u).2,tsum_mul_left]
      ring
    _ = P*∑' n,∑ u : Residues r,w u*D u n := by
      rw [Summable.tsum_finsetSum (fun u _ => (hE u).1.mul_left (w u))]
    _ = _ := by simp_rw [ht]

end CubicFirstMoment

end

end OAI
