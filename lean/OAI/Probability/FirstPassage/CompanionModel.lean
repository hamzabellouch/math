import OAI.Probability.FirstPassage.Translation
import OAI.Probability.LatticePassage.Environment
import Lean.Elab.Tactic.Omega

namespace OAI

namespace PlanarFPP
open MeasureTheory ProbabilityTheory Set

lemma companion_adj_step (p : Vertex) (d : Step) :
    CompanionFPP.lattice.Adj p (p+d.delta) := by
  cases d <;> simp [CompanionFPP.lattice, Step.delta]

lemma companion_adj_iff (p q : Vertex) :
    CompanionFPP.lattice.Adj p q ↔ ∃ d : Step, q=p+d.delta := by
  constructor
  · intro h
    change |p.1-q.1|+|p.2-q.2|=1 at h
    have hor : (q.1=p.1+1 ∧ q.2=p.2) ∨ (q.1=p.1-1 ∧ q.2=p.2) ∨
        (q.1=p.1 ∧ q.2=p.2+1) ∨ (q.1=p.1 ∧ q.2=p.2-1) := by
      simp only [abs_eq_max_neg] at h
      omega
    rcases hor with h | h | h | h
    · exact ⟨.east, by ext <;> simp_all [Step.delta,sub_eq_add_neg]⟩
    · exact ⟨.west, by ext <;> simp_all [Step.delta,sub_eq_add_neg]⟩
    · exact ⟨.north, by ext <;> simp_all [Step.delta,sub_eq_add_neg]⟩
    · exact ⟨.south, by ext <;> simp_all [Step.delta,sub_eq_add_neg]⟩
  · rintro ⟨d,rfl⟩
    exact companion_adj_step p d

def companionEdge (e : Edge) : CompanionFPP.Edge :=
  if e.2 = true then ⟨s(e.1,e.1+Step.north.delta), companion_adj_step _ _⟩
  else ⟨s(e.1,e.1+Step.east.delta), companion_adj_step _ _⟩

lemma companionEdge_step (p : Vertex) (d : Step) :
    companionEdge (d.edge p) = ⟨s(p,p+d.delta),companion_adj_step p d⟩ := by
  apply Subtype.ext
  cases d <;> simp [companionEdge,Step.edge,Step.delta,Prod.ext_iff]

lemma companionEdge_injective : Function.Injective companionEdge := by
  rintro ⟨⟨px,py⟩,b⟩ ⟨⟨qx,qy⟩,c⟩ h
  have he := congrArg Subtype.val h
  cases b <;> cases c <;>
    simp [companionEdge,Step.delta,Prod.ext_iff] at he ⊢ <;>
    rcases he with h | h <;> omega

lemma companionEdge_surjective : Function.Surjective companionEdge := by
  rintro ⟨e,he⟩
  induction e using Sym2.inductionOn with
  | hf p q =>
    obtain ⟨d,rfl⟩ := (companion_adj_iff p q).mp he
    exact ⟨d.edge p,companionEdge_step p d⟩

noncomputable def companionEdgeEquiv : Edge ≃ CompanionFPP.Edge :=
  Equiv.ofBijective companionEdge ⟨companionEdge_injective,companionEdge_surjective⟩

noncomputable def companionWeights (w : Edge → ℝ) : CompanionFPP.Environment :=
  fun e => w (companionEdgeEquiv.symm e)

@[simp] lemma companionWeights_edge (w : Edge → ℝ) (e : Edge) :
    companionWeights w (companionEdge e)=w e := by
  change w (companionEdgeEquiv.symm (companionEdgeEquiv e))=w e
  rw [companionEdgeEquiv.symm_apply_apply]

@[simp] lemma companion_pathCost_copy (w : CompanionFPP.Environment)
    {p q p' q' : Vertex} (walk : CompanionFPP.lattice.Walk p q) (hp : p=p') (hq : q=q') :
    CompanionFPP.pathCost w (walk.copy hp hq) = CompanionFPP.pathCost w walk := by
  subst p'; subst q'; rfl

lemma steps_companion_walk (w : Edge → ℝ) (p : Vertex) (ds : List Step) :
    ∃ walk : CompanionFPP.lattice.Walk p (p+displacement ds),
      CompanionFPP.pathCost (companionWeights w) walk = pathCost w p ds := by
  induction ds generalizing p with
  | nil =>
    refine ⟨(SimpleGraph.Walk.nil : CompanionFPP.lattice.Walk p p).copy rfl (by simp),?_⟩
    rw [companion_pathCost_copy]
    rfl
  | cons d ds ih =>
    obtain ⟨walk,hw⟩ := ih (p+d.delta)
    have he : (p+d.delta)+displacement ds = p+displacement (d::ds) := by
      simp [add_assoc]
    refine ⟨(SimpleGraph.Walk.cons (companion_adj_step p d) walk).copy rfl he,?_⟩
    simp only [companion_pathCost_copy, CompanionFPP.pathCost_cons, CompanionFPP.edgeCost, pathCost, hw]
    rw [← companionEdge_step,companionWeights_edge]

lemma companion_walk_steps (w : Edge → ℝ) {p q : Vertex}
    (walk : CompanionFPP.lattice.Walk p q) :
    ∃ ds : List Step, p+displacement ds=q ∧ pathCost w p ds =
      CompanionFPP.pathCost (companionWeights w) walk := by
  induction walk with
  | nil => exact ⟨[],by simp,rfl⟩
  | @cons p u q hadj walk ih =>
    obtain ⟨d,rfl⟩ := (companion_adj_iff p u).mp hadj
    obtain ⟨ds,he,hc⟩ := ih
    refine ⟨d::ds,by simpa [add_assoc] using he,?_⟩
    simp only [pathCost,CompanionFPP.pathCost_cons,CompanionFPP.edgeCost,hc]
    rw [← companionEdge_step,companionWeights_edge]

theorem companion_passageTime_eq (w : Edge → ℝ) (p q : Vertex) :
    CompanionFPP.passageTime (companionWeights w) p q = passageTime w p q := by
  unfold CompanionFPP.passageTime passageTime
  congr 1
  ext t
  constructor
  · rintro ⟨walk,rfl⟩
    obtain ⟨ds,he,hc⟩ := companion_walk_steps w walk
    exact ⟨ds,he,hc⟩
  · rintro ⟨ds,he,rfl⟩
    obtain ⟨walk,hw⟩ := steps_companion_walk w p ds
    subst q
    exact ⟨walk,hw⟩

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {τ : Edge → Ω → ℝ}

theorem ExponentialEnvironment.companionLaw (h : ExponentialEnvironment P τ) :
    Measure.map (fun ω => companionWeights (fun e => τ e ω)) P =
      CompanionFPP.environmentLaw := by
  have hi := h.independent.precomp companionEdgeEquiv.symm.injective
  unfold companionWeights
  rw [hi.map_fun_eq_infinitePi_map (fun _ => h.measurable _)]
  simp only [h.marginal,CompanionFPP.environmentLaw]

lemma measurable_companionWeights (hτ : ∀ e, Measurable (τ e)) :
    Measurable (fun ω => companionWeights (fun e => τ e ω)) :=
  Measurable.of_eval (fun _ => hτ _)

end PlanarFPP

end OAI
