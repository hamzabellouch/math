import Mathlib
import OAI.Probability.LogConcave.Sampling.CenteringVelocityJoint

namespace OAI

section
noncomputable section
namespace LogConcaveSampling
open Set MeasureTheory Quadrature
open scoped Classical BigOperators NNReal

def velocityJointLip (n m : ℕ) (A lam : ℝ≥0) (r T h ψ s : ℝ) : ℝ≥0 :=
  2*(‖-(r*s)⁻¹‖₊*((∑i,‖terminalQuadratureWeight T h n i‖₊)*
    ((∑i : Fin (m+1),‖derivativeWeight (angleNodes m) i/ψ‖₊)*
      (16*(A*probabilityMeanLipschitz lam r))))+
    ‖s⁻¹‖₊*Real.toNNReal ((Real.pi^2/2)*T*((lam:ℝ)*r)))

theorem centeringVelocityJoint_lipschitz (n : ℕ) :
    ∃A B : ℝ≥0,∀{d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0},
      Primitive F lam → ∀(x : Point d) {r T h ψ s : ℝ},0<r →
        (lam:ℝ)*r^2 ≤ 1/2 → 0<T → T<1 → 0<h → 0<ψ → 0<s →
        ∀m : ℕ,ψ*m ≤ 1 → A*probabilityMeanLipschitz lam r ≤ 1/2 →
        B*probabilityMeanLipschitz lam r ≤ 1/2 → ∀N : ℕ,∀e : ProbabilityNode T h (n+1),
      LipschitzWith (velocityJointLip n m A lam r T h ψ s)
        (centeringVelocityJoint F x r T h ψ s n m N e) := by
  obtain ⟨A,B,hAB⟩ := centeringVelocityPicard_lipschitz n
  refine ⟨A,B,?_⟩
  intro d F lam hF x r T h ψ s hr hl hT0 hT1 hh hψ hs m hψm hq hq' N e
  have h := (productPointEquiv_symm_lipschitz_two d d).comp
    ((hAB hF x hr hl hT0 hT1 hh hψ hs m hψm hq hq' N e).comp
      (productPointEquiv_lipschitz_one d d))
  have ht : Real.toNNReal ((Real.pi^2/2)*T*((lam:ℝ)*r))=
      ⟨(Real.pi^2/2)*T*((lam:ℝ)*r),by positivity⟩ := by
    apply NNReal.eq
    exact Real.coe_toNNReal _ (by positivity)
  convert! h using 1
  rw [velocityJointLip,ht,mul_one]

lemma velocityJointLip_coefficient {r s T h ψ : ℝ}
    (hr : 0<r) (hs : 0<s) (hψ : 0<ψ) (hT0 : 0<T) (hT1 : T<1)
    (lam A : ℝ≥0) (n m : ℕ) :
    (velocityJointLip n m A lam r T h ψ s:ℝ) ≤
      Real.pi^2*((lam:ℝ)*r/s)*
        (16*A*(∑i,|terminalQuadratureWeight T h n i|)*
          ((∑i : Fin (m+1),|derivativeWeight (angleNodes m) i|)/ψ)+1) := by
  have hh := mul_le_mul_of_nonneg_left
    (centeringVelocityPicard_lipschitz_coefficient (h:=h) hr hs hψ hT0 hT1 lam A n m) (by norm_num : (0:ℝ) ≤ 2)
  have ht : Real.toNNReal ((Real.pi^2/2)*T*((lam:ℝ)*r))=
      ⟨(Real.pi^2/2)*T*((lam:ℝ)*r),by positivity⟩ := by
    apply NNReal.eq
    exact Real.coe_toNNReal _ (by positivity)
  convert! hh using 1
  · rw [velocityJointLip,ht]
    rfl
  · ring

end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling
open Set MeasureTheory ProbabilityTheory Quadrature RMSIntegral TensorEnergy
open scoped Classical BigOperators NNReal

theorem centeringVelocityJoint_full_rms (n : ℕ) :
    ∃Ap Ah Lp Lh : ℝ≥0,∃C J D : ℝ,0≤C ∧ 1≤J ∧ 1≤D ∧ ∃k : ℕ,
      ∀{d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0},∀hF : Primitive F lam,
      ∀(x : Point d) {r : ℝ},∀hr : 0<r,0<lam → ∀hl : (lam:ℝ)*r^2≤1/2,1≤d →
      ∀{T h : ℝ},∀hT0 : 0<T,∀hT1 : T<1,∀hh : 0<h,h≤Real.log 2 → h≤logMeshLength T →
      Ap*probabilityMeanLipschitz lam r≤1/2 → Ah*probabilityMeanLipschitz lam r≤1/2 →
      Lp*probabilityMeanLipschitz lam r≤1/2 → Lh*probabilityMeanLipschitz lam r≤1/2 →
      ∀N : ℕ,∀R : ℝ,0<R → R^2≤1-T^2 → ∀m : ℕ,1 ≤ m → ∀ψ : ℝ,0<ψ → ψ*m≤1 → ∀s : ℝ,
      let w := terminalQuadratureWeight T h n
      let err := fun y : Point (d+d) =>
        centeringVelocityJoint F x r T h ψ s n m N (probabilityEndpoint hT0 hT1 hh (n+1)) y-
          skewLieField (centeringPotential F x r T)
            (jointSkew (centeringKernel hF x hr hl hT0.le hT1) s) y
      Integrable (fun y => ‖err y‖^2) (gibbs (centeringPotential F x r T)) ∧
      (∫y,‖err y‖^2 ∂gibbs (centeringPotential F x r T)) ≤
        (r*s)⁻¹^2*(2*((∑v,|w v|)*(∑v,|w v| *
          kernelActionRmsBudget F x lam Ap Ah Lp r R (probabilityNodeTime T h (n+1) v) h ψ C J k (n+1) m N))+
        2*kernelAnalyticBudget n d lam r T h D) := by
  obtain ⟨Ap,Ah,Lp,Lh,C,J,D,hC,hJ,hD,k,hfull⟩ := kernelQuadraturePicard_full_rms n
  refine ⟨Ap,Ah,Lp,Lh,C,J,D,hC,hJ,hD,k,?_⟩
  intro d F lam hF x r hr hlam hl hd T h hT0 hT1 hh hs hL hqp hqh hqlp hqlh N R hR hRT m hm ψ hψ hψm s
  have hhfull := hfull hF x hr hlam hl hd hT0 hT1 hh hs hL hqp hqh hqlp hqlh N R hR hRT m hm ψ hψ hψm
  apply centeringVelocityJoint_rms_of_kernel hF x hr hlam hl hT0.le hT1 n m N
    (probabilityEndpoint hT0 hT1 hh (n+1)) _ hhfull.1 hhfull.2
  apply continuous_finsetSum
  intro i _
  exact (continuous_const_smul (terminalQuadratureWeight T h n i)).comp
    (kernelActionPicard_continuous hF x hr.le hl hT0 hT1 hh ψ (n+1) (by omega) m N i _)
end LogConcaveSampling

end

end

end OAI
