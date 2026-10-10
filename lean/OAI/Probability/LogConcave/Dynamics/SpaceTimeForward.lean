import Mathlib
import OAI.Probability.LogConcave.Dynamics.Curve

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology

section UpperProof
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
open Function MeasureTheory Set Filter
open scoped Topology NNReal

namespace LogConcaveSampling.GlobalODE
open Set Function Filter Metric
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {a b : ℝ} (hab : a≤b) {f : ℝ → E → E} (hc : Continuous (uncurry f))
    {K : ℝ≥0} (hL : ∀ t∈Icc a b,LipschitzWith K (f t))

def spaceTimeForward (p : ℝ × E) : ℝ × E :=
  (p.1,flow hL hc ⟨a,le_rfl,hab⟩ p.2 (projIcc a b hab p.1))
def spaceTimeBackward (p : ℝ × E) : ℝ × E :=
  (p.1,flow hL hc (projIcc a b hab p.1) p.2 a)

lemma spaceTimeForward_continuous : Continuous (spaceTimeForward hab hc hL) :=
  continuous_fst.prodMk ((flow_joint_continuous hL hc ⟨a,le_rfl,hab⟩).comp
    (continuous_snd.prodMk ((continuous_projIcc (h:=hab)).comp continuous_fst)))

lemma spaceTime_left_inverse : LeftInverse (spaceTimeBackward hab hc hL) (spaceTimeForward hab hc hL) := by
  intro p
  apply Prod.ext
  · rfl
  change flow hL hc (projIcc a b hab p.1)
    (flow hL hc ⟨a,le_rfl,hab⟩ p.2 (projIcc a b hab p.1)) a=p.2
  rw [flow_cocycle hL hc ⟨a,le_rfl,hab⟩ (projIcc a b hab p.1) ⟨a,le_rfl,hab⟩,flow_initial]
lemma spaceTime_right_inverse : RightInverse (spaceTimeBackward hab hc hL) (spaceTimeForward hab hc hL) := by
  intro p
  apply Prod.ext
  · rfl
  change flow hL hc ⟨a,le_rfl,hab⟩ (flow hL hc (projIcc a b hab p.1) p.2 a)
    (projIcc a b hab p.1)=p.2
  rw [flow_cocycle hL hc (projIcc a b hab p.1) ⟨a,le_rfl,hab⟩ (projIcc a b hab p.1),flow_initial]

lemma spaceTimeBackward_continuous : Continuous (spaceTimeBackward hab hc hL) := by
  apply continuous_fst.prodMk
  rw [continuous_iff_continuousAt]
  intro p
  let z := (spaceTimeBackward hab hc hL p).2
  let B := Real.exp ((K:ℝ)*(b-a))
  have hB : 0<B := Real.exp_pos _
  have he : flow hL hc ⟨a,le_rfl,hab⟩ z (projIcc a b hab p.1)=p.2 :=
    congrArg Prod.snd (spaceTime_right_inverse hab hc hL p)
  have hh : Continuous (fun q : ℝ × E =>
      q.2-flow hL hc ⟨a,le_rfl,hab⟩ z (projIcc a b hab q.1)) :=
    continuous_snd.sub ((flow_continuous hL hc ⟨a,le_rfl,hab⟩ z).comp
      (continuous_subtype_val.comp ((continuous_projIcc (h:=hab)).comp continuous_fst)))
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hn : ∀ᶠ q in 𝓝 p,‖q.2-flow hL hc ⟨a,le_rfl,hab⟩ z (projIcc a b hab q.1)‖<ε/B := by
    have he0 : p.2-flow hL hc ⟨a,le_rfl,hab⟩ z (projIcc a b hab p.1)=0 := by rw [he,sub_self]
    simpa only [he0,dist_zero_right] using (Metric.tendsto_nhds.mp (hh.tendsto p)) (ε/B) (div_pos hε hB)
  filter_upwards [hn] with q hq
  have hdist := (flow_lipschitz hL hc (projIcc a b hab q.1) ⟨a,le_rfl,hab⟩).dist_le_mul q.2
    (flow hL hc ⟨a,le_rfl,hab⟩ z (projIcc a b hab q.1))
  rw [flow_cocycle hL hc ⟨a,le_rfl,hab⟩ (projIcc a b hab q.1) ⟨a,le_rfl,hab⟩,flow_initial] at hdist
  change dist (flow hL hc (projIcc a b hab q.1) q.2 a) z<ε
  apply hdist.trans_lt
  have hmax : Real.exp ((K:ℝ)*|a-(projIcc a b hab q.1:ℝ)|)≤B := by
    apply Real.exp_le_exp.mpr
    apply mul_le_mul_of_nonneg_left _ K.coe_nonneg
    rw [abs_of_nonpos (sub_nonpos.mpr (projIcc a b hab q.1).2.1)]
    linarith [(projIcc a b hab q.1).2.2]
  apply (mul_le_mul_of_nonneg_right hmax dist_nonneg).trans_lt
  rw [dist_eq_norm,mul_comm]
  exact (lt_div_iff₀ hB).mp hq

def spaceTimeHomeomorph : (ℝ × E) ≃ₜ (ℝ × E) where
  toFun := spaceTimeForward hab hc hL
  invFun := spaceTimeBackward hab hc hL
  left_inv := spaceTime_left_inverse hab hc hL
  right_inv := spaceTime_right_inverse hab hc hL
  continuous_toFun := spaceTimeForward_continuous hab hc hL
  continuous_invFun := spaceTimeBackward_continuous hab hc hL
end LogConcaveSampling.GlobalODE

end UpperProof
end
end
end

end OAI
