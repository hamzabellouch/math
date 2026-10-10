import OAI.NumberTheory.CubicMoment.Theta.CubicThetaResidueLocalCoefficient

namespace OAI

/-! The actual nonzero-angular summation formula with the finite cusp
average evaluated as its exact Ramanujan Euler product. -/
noncomputable section
open scoped BigOperators ContDiff
namespace CubicFirstMoment

def cubicThetaLocalDualTerm (r : Eisenstein) (rev : Bool) (k : ℕ)
    (W : ℝ→ℂ) (σ X : ℝ) (n : MetaplecticDualArgument) : ℂ :=
  theta (cubicThetaCircleOrder rev k) n.val*
    (cubicThetaCommonCuspCoefficient n.val*metaplecticLocalCoefficient r n)/
      (‖cubicThetaFrequency n.val‖:ℂ)*
        metaplecticTransform (cubicThetaCircleOrder (!rev) k) W σ
          (cubicThetaDualScale r (X/27)*‖cubicThetaFrequency n.val‖^2)

lemma cubicThetaResidueDualTerm_local {r : Eisenstein} (hr : primary r)
    (hs : Squarefree r) [Fintype (Residues r)] (rev : Bool) (k : ℕ)
    (W : ℝ→ℂ) (σ X : ℝ) :
    cubicThetaResidueDualTerm r hr rev k W σ X=cubicThetaLocalDualTerm r rev k W σ X := by
  funext n
  unfold cubicThetaResidueDualTerm cubicThetaLocalDualTerm
  rw [cubicThetaResidueDualCoefficient_local hr hs]

theorem cubicThetaLocal_voronoi {r : Eisenstein} (hr : primary r) (hs : Squarefree r)
    [Fintype (Residues r)] (rev : Bool) {k : ℕ} (hk : 0<k)
    (W : ℝ→ℂ) (hW : HasCompactSupport W) (hpos : tsupport W ⊆ Set.Ioi 0)
    (hsm : ContDiff ℝ ∞ W) {σ X : ℝ} (hσ : 0<σ) (hX : 0<X) :
    Summable (cubicThetaLocalDualTerm r rev k W σ X) ∧
    ((((3^(5/2:ℝ):ℝ):ℂ)*theta (cubicThetaCircleOrder (!rev) k) lambdaE)*
      ((Real.sqrt (norm r):ℂ)*gauss r))*
        metaplecticRawCompleted r (cubicThetaCircleOrder (!rev) k) W X=
    (cubicThetaLevelAngularRoot r rev k)⁻¹*cubicThetaDualPrefactor r*
      ∑' n,cubicThetaLocalDualTerm r rev k W σ X n := by
  have H := cubicThetaResidue_voronoi hr hs rev hk W hW hpos hsm hσ hX
  rwa [cubicThetaResidueDualTerm_local hr hs] at H

end CubicFirstMoment

end

end OAI
