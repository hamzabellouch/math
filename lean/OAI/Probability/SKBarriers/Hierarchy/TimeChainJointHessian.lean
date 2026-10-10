import Mathlib
import OAI.Probability.SKBarriers.Replicas.TripleScaleStats
import OAI.Probability.SKBarriers.Hierarchy.TimeIncrementBridge
import OAI.Probability.SKBarriers.Parisi.CDFCramer
import OAI.Probability.SKBarriers.Parisi.CDFSquareSusceptibility
import OAI.Probability.SKBarriers.Scalar.PositiveTimeChain
import OAI.Probability.SKBarriers.Scalar.ScalarJointLoss

namespace OAI

section

noncomputable section
open scoped BigOperators NNReal Topology
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

def timeChainJointHessian (β : ℝ) (l j k : List (ℝ × ℝ≥0)) : ℝ :=
  let F := scalarTimeChain β k scalarSpinTerminal
  let H := scalarTimeChain β j F
  scalarTimeChainAverage β l H (fun x => rootHessian 0 H x*
    scalarTimeChainAverage β j F (rootHessian 0 F) x) 0

theorem timeChainJointHessian_loss (β : ℝ) (l j k : List (ℝ × ℝ≥0))
    (hl : ∀ p∈l,p.1∈Icc (0:ℝ) 1) (hjk : ∀ p∈j++k,p.1∈Icc (0:ℝ) 1)
    (hsl : l.Pairwise (fun p q => p.1≤q.1)) (hsjk : (j++k).Pairwise (fun p q => p.1≤q.1))
    {a : ℝ} (ha : 0≤a) (hma : ∀ p∈j,a≤p.1)
    (hvl : (chainDuration l:ℝ)≤1) (hvjk : (chainDuration (j++k):ℝ)≤1) :
    timeChainJointHessian β l j k ≤
      scalarTimeChainAverage β l (scalarTimeChain β (j++k) scalarSpinTerminal)
        (fun x => (rootHessian 0 (scalarTimeChain β (j++k) scalarSpinTerminal) x)^2) 0-
        a*(β^2*(chainDuration j:ℝ))*(scalarSusceptibilityFloor (β^2) (1+2*β^2+4*(β^2)^2))^3/2 := by
  let L := scaleIncrementChain β (rawTimeChain l)
  let J := scaleIncrementChain β (rawTimeChain j)
  let K := scaleIncrementChain β (rawTimeChain k)
  have heb : J++K=scaleIncrementChain β (rawTimeChain (j++k)) := by
    rw [rawTimeChain_append,scaleIncrementChain_append]
  have G := scalarIncrementAverage_joint_hessian_loss L J K
    (scaleIncrementChain_mass β _ (rawTimeChain_mass _ hl))
    (heb ▸ scaleIncrementChain_mass β _ (rawTimeChain_mass _ hjk))
    (scaleIncrementChain_sorted β _ (rawTimeChain_sorted _ hsl))
    (heb ▸ scaleIncrementChain_sorted β _ (rawTimeChain_sorted _ hsjk))
    (T:=β^2) (sq_nonneg β) ha
    (scaleIncrementChain_mass β _ (rawTimeChain_mass _ hma))
    (by dsimp [L]; rw [rawVariance_scale,rawVariance_rawTimeChain]; nlinarith [sq_nonneg β])
    (by rw [heb,rawVariance_scale,rawVariance_rawTimeChain]; nlinarith [sq_nonneg β])
  dsimp only at G
  simp only [L,J,K,rawVariance_scale,rawVariance_rawTimeChain,scalarIncrementChain_rawTimeChain,
    scalarIncrementAverage_rawTimeChain] at G
  simpa only [timeChainJointHessian,scalarTimeChain_append] using G

theorem timeChainJointHessian_cdf_loss (β : ℝ) {α : ℝ → ℝ}
    (ha : ∀ z,α z∈Icc (0:ℝ) 1) (hm : Monotone α) {r q : ℝ}
    (hr : 0≤r) (hrq : r≤q) (hq : q≤1)
    (l j k : List (ℝ × ℝ≥0))
    (hdl : (chainDuration l:ℝ)=r) (hdj : (chainDuration j:ℝ)=q-r) (hdk : (chainDuration k:ℝ)=1-q)
    (hl : TimeChainModels α 0 l) (hj : TimeChainModels α r j) (hk : TimeChainModels α q k)
    (hml : ∀ p∈l,p.1∈Icc (0:ℝ) 1) (hmj : ∀ p∈j,p.1∈Icc (0:ℝ) 1) (hmk : ∀ p∈k,p.1∈Icc (0:ℝ) 1)
    (hpl : ∀ p∈l,0<p.2) (hpj : ∀ p∈j,0<p.2) (hpk : ∀ p∈k,0<p.2) :
    timeChainJointHessian β l j k ≤ scalarCDFSusceptibilitySquareAverage β α r-
      α r*(β^2*(q-r))*(scalarSusceptibilityFloor (β^2) (1+2*β^2+4*(β^2)^2))^3/2 := by
  have hdjk : (chainDuration (j++k):ℝ)=1-r := by
    rw [chainDuration_append,NNReal.coe_add,hdj,hdk]; ring
  have hjk : TimeChainModels α r (j++k) := hj.append (by simpa only [hdj,add_sub_cancel] using hk)
  have hmjk : ∀ p∈j++k,p.1∈Icc (0:ℝ) 1 := by
    intro p hp; exact (List.mem_append.mp hp).elim (hmj p) (hmk p)
  have hpjk : ∀ p∈j++k,0<p.2 := by
    intro p hp; exact (List.mem_append.mp hp).elim (hpj p) (hpk p)
  have G := timeChainJointHessian_loss β l j k hml hmjk (hl.sorted hm hpl) (hjk.sorted hm hpjk)
    (ha r).1 (fun p hp => (hj.mass_bounds hm hp (hpj p hp)).1)
    (by rw [hdl]; exact hrq.trans hq) (by rw [hdjk]; linarith)
  rw [hdj] at G
  let sr := Real.toNNReal (1-r)
  let tr := Real.toNNReal r
  have hsr : (sr:ℝ)=1-r := Real.coe_toNNReal _ (by linarith)
  have htr : (tr:ℝ)=r := Real.coe_toNNReal _ hr
  have hsr1 : sr≤1 := by rw [← NNReal.coe_le_coe,hsr,NNReal.coe_one]; linarith
  have htr1 : tr≤1 := by rw [← NNReal.coe_le_coe,htr,NNReal.coe_one]; linarith
  have he : scalarTimeChain β (j++k) scalarSpinTerminal=scalarCDFValue β α r sr := by
    funext x
    exact (scalarCDFOperator_eq_chain scalarSpinTerminal_regular scalarSpinTerminal_lipschitz
      β ha hm (j++k) hmjk r sr hsr1 (NNReal.coe_injective (hdjk.trans hsr.symm)) hjk x).symm
  rw [he,scalarCDFValue_rootHessian β ha hm r sr hsr1] at G
  have hav := scalarCDFAverage_eq_chainAverage_lipschitz
    (scalarCDFValue_regular β ha hm r sr hsr1) (scalarCDFValue_lipschitz β ha hm r sr hsr1)
    (scalarCDFHessian_square_lipschitz β ha hm r sr hsr1)
    (B:=1) (scalarCDFHessian_square_bound β ha hm r sr hsr1) β ha hm l hml 0 tr htr1
    (NNReal.coe_injective (hdl.trans htr.symm)) hl 0
  rw [← hav] at G
  exact G

end SK.Analytic

end
end

end OAI
