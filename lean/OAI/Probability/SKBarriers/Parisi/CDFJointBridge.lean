import Mathlib
import OAI.Probability.SKBarriers.Hierarchy.TimeChainOn
import OAI.Probability.SKBarriers.Hierarchy.TimeChainJointHessian
import OAI.Probability.SKBarriers.Parisi.CDFJointSusceptibility

namespace OAI

section

noncomputable section
open scoped NNReal Topology
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

theorem timeChainJointHessian_eq_cdf (β : ℝ) {α : ℝ → ℝ}
    (ha : ∀ z,α z∈Icc (0:ℝ) 1) (hm : Monotone α) {r q : ℝ}
    (hr : 0≤r) (hrq : r≤q) (hq : q≤1)
    (l : TimeChainOn α 0 r) (j : TimeChainOn α r q) (k : TimeChainOn α q 1) :
    timeChainJointHessian β l.chain j.chain k.chain=scalarCDFJointSusceptibility β α r q := by
  let tr := Real.toNNReal r
  let tj := Real.toNNReal (q-r)
  let sr := Real.toNNReal (1-r)
  let sq := Real.toNNReal (1-q)
  have htr : (tr:ℝ)=r := Real.coe_toNNReal _ hr
  have htj : (tj:ℝ)=q-r := Real.coe_toNNReal _ (sub_nonneg.mpr hrq)
  have hsr : (sr:ℝ)=1-r := Real.coe_toNNReal _ (by linarith)
  have hsq : (sq:ℝ)=1-q := Real.coe_toNNReal _ (by linarith)
  have htr1 : tr≤1 := by rw [← NNReal.coe_le_coe,htr,NNReal.coe_one]; linarith
  have htj1 : tj≤1 := by rw [← NNReal.coe_le_coe,htj,NNReal.coe_one]; linarith
  have hsr1 : sr≤1 := by rw [← NNReal.coe_le_coe,hsr,NNReal.coe_one]; linarith
  have hsq1 : sq≤1 := by rw [← NNReal.coe_le_coe,hsq,NNReal.coe_one]; linarith
  have heF : scalarTimeChain β k.chain scalarSpinTerminal=scalarCDFValue β α q sq := by
    funext x
    exact (scalarCDFOperator_eq_chain scalarSpinTerminal_regular scalarSpinTerminal_lipschitz β ha hm
      k.chain k.mass q sq hsq1 (NNReal.coe_injective (k.duration.trans hsq.symm)) k.models x).symm
  have heH : scalarTimeChain β j.chain (scalarTimeChain β k.chain scalarSpinTerminal)=scalarCDFValue β α r sr := by
    rw [← scalarTimeChain_append]
    funext x
    exact (scalarCDFOperator_eq_chain scalarSpinTerminal_regular scalarSpinTerminal_lipschitz β ha hm
      (j.append k).chain (j.append k).mass r sr hsr1
      (NNReal.coe_injective ((j.append k).duration.trans hsr.symm)) (j.append k).models x).symm
  have heK : scalarTimeChainAverage β j.chain (scalarTimeChain β k.chain scalarSpinTerminal)
      (rootHessian 0 (scalarTimeChain β k.chain scalarSpinTerminal))=scalarCDFConditionalSusceptibility β α r q := by
    rw [heF,scalarCDFValue_rootHessian β ha hm q sq hsq1]
    funext x
    exact (scalarCDFAverage_eq_chainAverage_lipschitz
      (scalarCDFValue_regular β ha hm q sq hsq1) (scalarCDFValue_lipschitz β ha hm q sq hsq1)
      (scalarCDFHessian_lipschitz β ha hm q sq hsq1) (B:=1)
      (scalarCDFHessian_abs_le_one β ha hm q sq hsq1)
      β ha hm j.chain j.mass r tj htj1 (NNReal.coe_injective (j.duration.trans htj.symm)) j.models x).symm
  dsimp only [timeChainJointHessian]
  rw [heH,heK,scalarCDFValue_rootHessian β ha hm r sr hsr1]
  have hK := scalarCDFConditionalSusceptibility_regular β ha hm hr hrq hq
  have hp := unitBoundedProduct_lipschitz (scalarCDFHessian_lipschitz β ha hm r sr hsr1) hK.1
    (scalarCDFHessian_abs_le_one β ha hm r sr hsr1) hK.2
  have hb (x) : |scalarCDFHessian β α r sr x*scalarCDFConditionalSusceptibility β α r q x|≤(1:ℝ≥0) := by
    rw [abs_mul,NNReal.coe_one]
    exact (mul_le_mul (scalarCDFHessian_abs_le_one β ha hm r sr hsr1 x) (hK.2 x)
      (abs_nonneg _) (by norm_num)).trans_eq (by ring)
  exact (scalarCDFAverage_eq_chainAverage_lipschitz
    (scalarCDFValue_regular β ha hm r sr hsr1) (scalarCDFValue_lipschitz β ha hm r sr hsr1) hp hb
    β ha hm l.chain l.mass 0 tr htr1
    (NNReal.coe_injective (by rw [l.duration,sub_zero,htr])) l.models 0).symm

theorem scalarCDFJointSusceptibility_quantile_loss {n : ℕ} (β : ℝ) (Q : Fin (n+1) → ℝ)
    (hQ : Q∈admissibleQuantiles n) {r q : ℝ} (hr : 0≤r) (hrq : r≤q) (hq : q≤1) :
    scalarCDFJointSusceptibility β (quantileCDF n Q) r q ≤
      scalarCDFSusceptibilitySquareAverage β (quantileCDF n Q) r-
      quantileCDF n Q r*(β^2*(q-r))*(scalarSusceptibilityFloor (β^2) (1+2*β^2+4*(β^2)^2))^3/2 := by
  obtain ⟨l⟩ := exists_quantile_TimeChainOn β Q hQ (s:=0) le_rfl hr (hrq.trans hq)
  obtain ⟨j⟩ := exists_quantile_TimeChainOn β Q hQ hr hrq hq
  obtain ⟨k⟩ := exists_quantile_TimeChainOn β Q hQ (hr.trans hrq) hq le_rfl
  have G := timeChainJointHessian_cdf_loss β (quantileCDF_bounds n Q) (quantileCDF_monotone n Q)
    hr hrq hq l.chain j.chain k.chain (by simpa only [sub_zero] using l.duration) j.duration k.duration
    l.models j.models k.models l.mass j.mass k.mass l.positive j.positive k.positive
  rw [timeChainJointHessian_eq_cdf β (quantileCDF_bounds n Q) (quantileCDF_monotone n Q) hr hrq hq l j k] at G
  exact G

end SK.Analytic

end
end

end OAI
