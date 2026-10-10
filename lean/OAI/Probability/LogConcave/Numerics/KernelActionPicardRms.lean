import Mathlib
import OAI.Probability.LogConcave.Dynamics.ConditionalHarmonicFlow
import OAI.Probability.LogConcave.Complexity.KernelValueRmsBudget

namespace OAI

section
section
noncomputable section
namespace LogConcaveSampling
open Set MeasureTheory ProbabilityTheory RMSIntegral Quadrature
open scoped Classical BigOperators NNReal

theorem kernelActionPicard_rms (n : ℕ) (hn : 0<n) :
    ∃Ap Ah Lp Lh : ℝ≥0,∃C J : ℝ,0≤C ∧ 1≤J ∧ ∃k : ℕ,
      ∀{d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0},∀hF : Primitive F lam,
      ∀(x : Point d) {r : ℝ},∀hr : 0<r,0<lam → ∀hl : (lam:ℝ)*r^2≤1/2,1≤d →
      ∀{T h : ℝ},∀hT0 : 0<T,∀hT1 : T<1,∀hh : 0<h,h≤Real.log 2 →
      Ap*probabilityMeanLipschitz lam r≤1/2 → Ah*probabilityMeanLipschitz lam r≤1/2 →
      Lp*probabilityMeanLipschitz lam r≤1/2 → Lh*probabilityMeanLipschitz lam r≤1/2 →
      ∀N : ℕ,∀s e : ProbabilityNode T h n,
      let S : Icc (0:ℝ) T := ⟨probabilityNodeTime T h n s,probabilityNodeTime_mem hT0 hT1 hh hn s⟩
      let E : Icc (0:ℝ) T := ⟨probabilityNodeTime T h n e,probabilityNodeTime_mem hT0 hT1 hh hn e⟩
      let μ := gibbs (centeringPotential F x r S)
      let fw := probabilityTransport hF x hr.le hl hT0.le hT1 S E
      ∀R : ℝ,0<R → R^2≤1-T^2 →
      ∀m : ℕ,1 ≤ m → ∀ψ : ℝ,0<ψ → ψ*m≤1 →
      let err := fun y => kernelActionPicard F x r T h ψ n m N s e
        (fw (productPointEquiv d d y).1,(productPointEquiv d d y).2)-kernelTransportAction fw y
      Integrable (fun y => ‖err y‖^2) μ ∧
      (∫y,‖err y‖^2 ∂μ)≤
        2*((∑i,|derivativeWeight (angleNodes m) i/ψ|)*
          (∑i,|derivativeWeight (angleNodes m) i/ψ| *
            kernelValueRmsBudget F x lam Ap Ah Lp r R S h (ψ*angleNodes m i) C J k n N))+
        2*(((∑i,|derivativeWeight (angleNodes m) i|)/ψ)^2*
          (((ψ*m)^(m+1)/(m.factorial:ℝ))^2*
            ((d*((lam:ℝ)*r^2)^2)*(R⁻¹)^(4*(m+1))*harmonicCorrectionBudget (m+1)))) := by
  obtain ⟨Ap,Ah,Lp,Lh,C,J,hC,hJ,k,hNum⟩ := kernelActionPicard_numerical_rms n hn
  refine ⟨Ap,Ah,Lp,Lh,C,J,hC,hJ,k,?_⟩
  intro d F lam hF x r hr hlam hl hd T h hT0 hT1 hh hsmall hqp hqh hqlp hqlh N s e
  dsimp only
  let S : Icc (0:ℝ) T := ⟨probabilityNodeTime T h n s,probabilityNodeTime_mem hT0 hT1 hh hn s⟩
  let E : Icc (0:ℝ) T := ⟨probabilityNodeTime T h n e,probabilityNodeTime_mem hT0 hT1 hh hn e⟩
  let μ := gibbs (centeringPotential F x r S)
  let fw := probabilityTransport hF x hr.le hl hT0.le hT1 S E
  intro R hR hRT m hm1 ψ hψ hψm
  have hRS : R^2≤1-(S:ℝ)^2 := by
    have hs := pow_le_pow_left₀ S.2.1 S.2.2 2
    linarith
  obtain ⟨Ξ,hc,hder,hmeas,hlaw⟩ := exists_conditional_harmonic_flow hF x hr.le hl S.2.1 (S.2.2.trans_lt hT1)
  have hnum := hNum hF x hr hlam hl hd hT0 hT1 hh hsmall hqp hqh hqlp hqlh N s e
    R hR hRS Ξ (fun y => (hc y).1) (fun y => (hc y).2) hder hmeas hlaw m ψ hψ hψm
  have hex := kernel_action_between_stencil_rms hF x hr hlam hl hR hRT hT0.le hT1 S E Ξ
    (fun y => (hc y).2) hder hmeas hlaw m hm1 ψ hψ hψm
  let pos := fun y : Point (d+d) => (productPointEquiv d d y).1
  let mom := fun y : Point (d+d) => (productPointEquiv d d y).2
  let inp := fun y => (fw (pos y),mom y)
  let w := fun z y => pos (Ξ y z)
  let num := fun y => kernelActionPicard F x r T h ψ n m N s e (inp y)
  let mid := fun y => derivativeStencil (angleNodes m) ψ
    (fun i => fw (w (ψ*angleNodes m i) y)-w (ψ*angleNodes m i) y)
  have hpos : Measurable pos := (productPointEquiv d d).continuous.measurable.fst
  have hmom : Measurable mom := (productPointEquiv d d).continuous.measurable.snd
  have hfw : Measurable fw := (probabilityTransport_continuous hF x hr.le hl hT0.le hT1 S E).measurable
  have hinp : Measurable inp := (hfw.comp hpos).prodMk hmom
  have hw (z : ℝ) : Measurable (w z) := hpos.comp (hmeas.comp (measurable_const.prodMk measurable_id))
  have hnm : Measurable num := by
    change Measurable (fun y => ∑i,(derivativeWeight (angleNodes m) i/ψ) •
      kernelCorrectionPicard F x r T h (ψ*angleNodes m i) n N s e (inp y))
    apply Finset.measurable_sum
    intro i _
    have hc : Continuous (fun v : Point d => (derivativeWeight (angleNodes m) i/ψ) • v) := continuous_const_smul _
    exact hc.measurable.comp
      ((kernelCorrectionPicard_continuous hF x hr.le hl hT0 hT1 hh (ψ*angleNodes m i) n hn N s e).measurable.comp hinp)
  have hmid : Measurable mid := by
    apply Finset.measurable_sum
    intro i _
    have hc : Continuous (fun v : Point d => (derivativeWeight (angleNodes m) i/ψ) • v) := continuous_const_smul _
    exact hc.measurable.comp
      ((hfw.comp (hw (ψ*angleNodes m i))).sub (hw (ψ*angleNodes m i)))
  exact add_error_sq hnm hmid hex.1 hnum.1 hex.2.1 hnum.2 hex.2.2
end LogConcaveSampling

end

end

end

end OAI
