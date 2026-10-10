import Mathlib
import OAI.Probability.LogConcave.Sampling.VelocityJointLip
import OAI.Probability.LogConcave.Complexity.KernelAnalyticNormalizedBudget
import OAI.Probability.LogConcave.Sampling.StationaryMeanTarget

namespace OAI

section
noncomputable section
namespace LogConcaveSampling
open Set MeasureTheory Quadrature ProbabilityTheory
open scoped Classical BigOperators NNReal

theorem centeringMeanCircuit_full_rms (n : ℕ) :
    ∃A B Ap Ah Lp Lh : ℝ≥0,∃C J D : ℝ,0 ≤ C ∧ 1 ≤ J ∧ 1 ≤ D ∧ ∃k : ℕ,
    ∀{d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0},∀hF : Primitive F lam,
    ∀(x : Point d) {r : ℝ},∀hr : 0<r,r ≤ 1 → 0<lam →
    ∀hl : (lam:ℝ)*r^2 ≤ 1/2,(lam:ℝ)*r ≤ 1 → 1 ≤ d →
    ∀{T h : ℝ},∀hT0 : 0<T,∀hT1 : T<1,∀hh : 0<h,h ≤ Real.log 2 → h ≤ logMeshLength T →
    Ap*probabilityMeanLipschitz lam r ≤ 1/2 → Ah*probabilityMeanLipschitz lam r ≤ 1/2 →
    Lp*probabilityMeanLipschitz lam r ≤ 1/2 → Lh*probabilityMeanLipschitz lam r ≤ 1/2 →
    A*probabilityMeanLipschitz lam r ≤ 1/2 → B*probabilityMeanLipschitz lam r ≤ 1/2 →
    ∀N : ℕ,∀R : ℝ,0<R → R^2 ≤ 1-T^2 → ∀m : ℕ,1 ≤ m → ∀ψ : ℝ,0<ψ → ψ*m ≤ 1 →
    ∀s : ℝ,0<s → ∀nc Nc : ℕ,0<nc →
    centeringRowBudget nc*velocityJointLip n m A lam r T h ψ s ≤ 1/2 →
    let e := probabilityEndpoint hT0 hT1 hh (n+1)
    let E := velocityNormalizedBudget d k n m N lam Ap Ah Lp r R T h ψ C J D
    let K := velocityJointLip n m A lam r T h ψ s
    let Z := centerStateEnvelope nc Nc ((lam:ℝ)*r/s) R (centeringRowBudget nc*K:ℝ≥0) E
    ∃X : StationaryPath (gibbs (centeringPotential F x r T))
      (skewLieField (centeringPotential F x r T)
        (jointSkew (centeringKernel hF x hr hl hT0.le hT1) s)),
      (∀i,Integrable (fun y => ‖stationaryPicard nc Nc
        (centeringVelocityJoint F x r T h ψ s n m N e) y i-X.path y (probabilityNodes nc i)‖^2)
        (gibbs (centeringPotential F x r T))) ∧
      (∀i,(∫y,‖stationaryPicard nc Nc
        (centeringVelocityJoint F x r T h ψ s n m N e) y i-X.path y (probabilityNodes nc i)‖^2
          ∂gibbs (centeringPotential F x r T)) ≤ (circuitD F x)^2*Z) ∧
      Measurable (stationaryMeanTarget hF x hr hl hT0.le hT1 X) ∧
      (gibbs (centeringPotential F x r T)).map (stationaryMeanTarget hF x hr hl hT0.le hT1 X)=
        (stdGaussian (Point d)).map (fun g => primitiveExpectedField F x r+s • g) ∧
      Integrable (fun y => ‖centeringMeanCircuit F x r T h ψ s n m N nc Nc e y-
        stationaryMeanTarget hF x hr hl hT0.le hT1 X y‖^2) (gibbs (centeringPotential F x r T)) ∧
      (∫y,‖centeringMeanCircuit F x r T h ψ s n m N nc Nc e y-
        stationaryMeanTarget hF x hr hl hT0.le hT1 X y‖^2 ∂gibbs (centeringPotential F x r T)) ≤
        (s*circuitD F x)^2*centerMeanEnvelope nc ((lam:ℝ)*r/s) R Z := by
  obtain ⟨A,B,hLip⟩ := centeringVelocityJoint_lipschitz n
  obtain ⟨Ap,Ah,Lp,Lh,C,J,D,hC,hJ,hD,k,hRms⟩ := centeringVelocityJoint_full_rms n
  refine ⟨A,B,Ap,Ah,Lp,Lh,C,J,D,hC,hJ,hD,k,?_⟩
  intro d F lam hF x r hr hr1 hlam hl hL hd T h hT0 hT1 hh hsmall hlarge hp hharm hlp hlh ha hb N R hR hRT m hm ψ hψ hψm s hs nc Nc hnc hq e E K Z
  have hhat := hLip hF x hr hl hT0 hT1 hh hψ hs m hψm ha hb N e
  have hv := hRms hF x hr hlam hl hd hT0 hT1 hh hsmall hlarge hp hharm hlp hlh N R hR hRT m hm ψ hψ hψm s
  have hE : 0 ≤ E := velocityNormalizedBudget_nonneg d k n m N lam Ap Ah Lp r R T h ψ C J D hR.le
  have hZ : 0 ≤ Z := centerStateEnvelope_nonneg nc Nc _ _ _ E (NNReal.coe_nonneg _) hE
  have hvel := velocityRmsBudget_normalized hF x Ap Ah Lp (C:=C) (J:=J) (D:=D) hr hr1 hR hT0 hT1 hh hψ hs hC (show 0≤J by linarith only [hJ]) hl hL k n m N
  obtain ⟨X⟩ := exists_centering_stationaryPath hF x hr hlam hl hT0.le hT1 hs
  have hstate (i : Fin (nc+1)) := centeringPicard_state_rms hF x hr hlam hl hR hRT hT0.le hT1 hs X
    n m N nc Nc hnc e hhat hq (show 0 ≤ (((lam:ℝ)*r/s)*circuitD F x)^2*E by positivity)
    hv.1 (hv.2.trans hvel) i
  have hstate' (i : Fin (nc+1)) : (∫y,‖stationaryPicard nc Nc
      (centeringVelocityJoint F x r T h ψ s n m N e) y i-X.path y (probabilityNodes nc i)‖^2
        ∂gibbs (centeringPotential F x r T)) ≤ (circuitD F x)^2*Z :=
    (hstate i).2.trans (centeringPicardBudget_normalized F x nc Nc lam K r R s E hE)
  have hmean := centeringMeanCircuit_rms hF x hr hlam hl hR hRT hT0.le hT1 hs X
    n m N nc Nc hnc e hhat (show 0 ≤ (circuitD F x)^2*Z by positivity)
    (fun i => (hstate i).1) hstate'
  refine ⟨X,(fun i => (hstate i).1),hstate',?_,
    stationaryMeanTarget_law hF x hr hlam hl hT0.le hT1 hs X,hmean.1,?_⟩
  · have he : stationaryMeanTarget hF x hr hl hT0.le hT1 X=
        fun y => primitiveExpectedField F x r+s • (productPointEquiv d d (X.path y 1)).2 := by
      funext y
      exact stationaryMeanTarget_identity hF x hr hlam hl hT0.le hT1 hs X y
    rw [he]
    exact measurable_const.add (((productPointEquiv d d).continuous.measurable.comp (X.measurable_slice 1)).snd.const_smul s)
  · exact hmean.2.trans (centeringMeanBudget_normalized F x nc lam r R hs hT0.le hT1.le hZ)
end LogConcaveSampling

end

end

end OAI
