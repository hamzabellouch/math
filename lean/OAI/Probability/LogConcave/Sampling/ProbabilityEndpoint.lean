import Mathlib
import OAI.Probability.LogConcave.Sampling.CenteringJointLaw
import OAI.Probability.LogConcave.Sampling.KernelTransportAction

namespace OAI

section
section
noncomputable section
namespace LogConcaveSampling
open Set MeasureTheory ProbabilityTheory
open scoped NNReal

lemma centering_transport_joint_law {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r T : ℝ} (hr : 0≤r)
    (hl : (lam:ℝ)*r^2≤1/2) (hT0 : 0≤T) (hT1 : T<1) (s e : Icc (0:ℝ) T) :
    (gibbs (centeringPotential F x r s)).map
      (fun y => (probabilityTransport hF x hr hl hT0 hT1 s e (productPointEquiv d d y).1,
        (productPointEquiv d d y).2))=
      (interpolationLaw F x r e).prod (stdGaussian (Point d)) := by
  let := interpolationLaw_probability hF x hr (by linarith) (s:ℝ)
  have hfw := (probabilityTransport_continuous hF x hr hl hT0 hT1 s e).measurable
  change (gibbs (centeringPotential F x r s)).map
    ((Prod.map (probabilityTransport hF x hr hl hT0 hT1 s e) id) ∘ productPointEquiv d d)=_
  rw [←Measure.map_map (hfw.prodMap measurable_id) (productPointEquiv d d).continuous.measurable,
    centering_joint_law hF x hr hl s.2.1 (s.2.2.trans_lt hT1),←Measure.map_prod_map _ _ hfw measurable_id,
    Measure.map_id,probabilityTransport_pushforward hF x hr hl hT0 hT1 s e]

lemma kernelTransportAction_terminal {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r T : ℝ} (hr : 0<r)
    (hl : (lam:ℝ)*r^2≤1/2) (hT0 : 0≤T) (hT1 : T<1)
    (s : Icc (0:ℝ) T) (p : Point (d+d)) :
    kernelTransportAction (probabilityTransport hF x hr.le hl hT0 hT1 s ⟨T,hT0,le_rfl⟩) p=
      (terminalJacobian hF x hr hl hT0 hT1
        (s,terminalForward hF x hr.le hl hT0 hT1 (s,(productPointEquiv d d p).1))-
          ContinuousLinearMap.id ℝ (Point d)) (productPointEquiv d d p).2 := by
  rw [terminalJacobian_eq,terminalBackward_forward]
  rfl

lemma rms_bound_pushforward {X Y E : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
    {μ : Measure X} {ν : Measure Y} {f : X → Y} (hf : Measurable f) (hlaw : μ.map f=ν)
    {e : Y → E} (he : Measurable e) (hi : Integrable (fun x => ‖e (f x)‖^2) μ)
    {B : ℝ} (hB : (∫x,‖e (f x)‖^2 ∂μ)≤B) :
    Integrable (fun y => ‖e y‖^2) ν ∧ (∫y,‖e y‖^2 ∂ν)≤B := by
  rw [←hlaw]
  refine ⟨(integrable_map_measure (he.norm.pow_const 2).aestronglyMeasurable hf.aemeasurable).mpr hi,?_⟩
  rw [integral_map hf.aemeasurable (he.norm.pow_const 2).aestronglyMeasurable]
  exact hB
end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling
open Set Quadrature

def probabilityEndpoint {T h : ℝ} (hT0 : 0<T) (hT1 : T<1) (hh : 0<h) (n : ℕ) :
    ProbabilityNode T h n :=
  (⟨logMeshCount T h-1,by have := logMeshCount_pos hT0 hT1 hh; omega⟩,Fin.last n)

lemma probabilityEndpoint_time {T h : ℝ} (hT0 : 0<T) (hT1 : T<1) (hh : 0<h)
    (n : ℕ) (hn : 0<n) : probabilityNodeTime T h n (probabilityEndpoint hT0 hT1 hh n)=T := by
  have hlast : probabilityNodes n (Fin.last n)=1 := by
    change (n:ℝ)/(n:ℝ)=1
    exact div_self (by exact_mod_cast hn.ne')
  have hN : logMeshCount T h-1+1=logMeshCount T h := by have := logMeshCount_pos hT0 hT1 hh; omega
  simp only [probabilityNodeTime,probabilityEndpoint,hlast,mul_one,probabilityCellLength]
  rw [hN,logMeshNode_last hT0 hT1 hh]
  ring
end LogConcaveSampling

end

end

end

end OAI
