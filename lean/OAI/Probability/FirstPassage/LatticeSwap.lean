import OAI.Probability.FirstPassage.ActualNoCorner

namespace OAI

namespace PlanarFPP
open MeasureTheory ProbabilityTheory Filter
open scoped Topology

def swapStep : Step → Step
  | .east => .north
  | .west => .south
  | .north => .east
  | .south => .west

@[simp] lemma swapStep_swap (d : Step) : swapStep (swapStep d)=d := by cases d <;> rfl
@[simp] lemma swapStep_delta (d : Step) : (swapStep d).delta=d.delta.swap := by cases d <;> rfl

def swapEdge (e : Edge) : Edge := (e.1.swap,!e.2)
@[simp] lemma swapEdge_swap (e : Edge) : swapEdge (swapEdge e)=e := by rcases e with ⟨p,b⟩; cases b <;> rfl
lemma swapEdge_injective : Function.Injective swapEdge := Function.LeftInverse.injective swapEdge_swap

lemma swapStep_edge (p : Vertex) (d : Step) : (swapStep d).edge p.swap=swapEdge (d.edge p) := by
  cases d <;> rfl

lemma displacement_swap (ds : List Step) : displacement (ds.map swapStep)=(displacement ds).swap := by
  induction ds with
  | nil => rfl
  | cons d ds ih => simp [ih,Prod.swap_add]

lemma pathCost_swap (w : Edge → ℝ) (p : Vertex) (ds : List Step) :
    pathCost w p.swap (ds.map swapStep)=pathCost (fun e => w (swapEdge e)) p ds := by
  induction ds generalizing p with
  | nil => rfl
  | cons d ds ih => simp [pathCost,swapStep_edge,← Prod.swap_add,ih]

lemma passageTime_swap (w : Edge → ℝ) (p q : Vertex) :
    passageTime w p.swap q.swap=passageTime (fun e => w (swapEdge e)) p q := by
  unfold passageTime
  congr 1
  ext t
  constructor
  · rintro ⟨ds,hend,hc⟩
    refine ⟨ds.map swapStep,?_,?_⟩
    · rw [displacement_swap]
      have hh := congrArg Prod.swap hend
      simpa only [Prod.swap_add,Prod.swap_swap] using hh
    · have hh := pathCost_swap (fun e => w (swapEdge e)) p.swap ds
      simpa only [Prod.swap_swap,swapEdge_swap,hc] using hh
  · rintro ⟨ds,hend,hc⟩
    exact ⟨ds.map swapStep,by rw [displacement_swap,← Prod.swap_add,hend],by rw [pathCost_swap,hc]⟩

noncomputable def swapPlane : Plane ≃ₗᵢ[ℝ] Plane :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (Equiv.swap 0 1)

@[simp] lemma swapPlane_zero (v : Plane) : swapPlane v 0=v 1 := by
  simp [swapPlane,LinearIsometryEquiv.piLpCongrLeft_apply,Equiv.piCongrLeft']
@[simp] lemma swapPlane_one (v : Plane) : swapPlane v 1=v 0 := by
  simp [swapPlane,LinearIsometryEquiv.piLpCongrLeft_apply,Equiv.piCongrLeft']
@[simp] lemma swapPlane_swap (v : Plane) : swapPlane (swapPlane v)=v := by
  ext i; fin_cases i <;> simp

lemma latticeFloor_swap (v : Plane) : latticeFloor (swapPlane v)=(latticeFloor v).swap := by
  simp [latticeFloor]

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {τ : Edge → Ω → ℝ}

lemma ExponentialEnvironment.swap (henv : ExponentialEnvironment P τ) :
    ExponentialEnvironment P (fun e => τ (swapEdge e)) where
  probability := henv.probability
  measurable _e := henv.measurable _
  independent := henv.independent.precomp swapEdge_injective
  marginal _e := henv.marginal _

theorem actualSourceTimeConstant_swap (henv : ExponentialEnvironment P τ) (v : Plane) :
    actualSourceTimeConstant (swapPlane v)=actualSourceTimeConstant v := by
  have ht : IsTimeConstant P (fun e => τ (swapEdge e)) (fun z => actualSourceTimeConstant (swapPlane z)) := by
    intro z
    filter_upwards [actualSourceTimeConstant_isTimeConstant henv (swapPlane z)] with ω hω
    have he (t : ℝ) : passageTime (fun e => τ (swapEdge e) ω) 0 (latticeFloor (t • z)) =
        passageTime (fun e => τ e ω) 0 (latticeFloor (t • swapPlane z)) := by
      rw [← passageTime_swap (fun e => τ e ω) (0 : Vertex) (latticeFloor (t • z)),← latticeFloor_swap,map_smul]
      rfl
    simpa only [show ((0,0) : Vertex)=0 from rfl,he] using hω
  have hh := actualSourceTimeConstant_unique henv.swap ht
  exact congrFun hh v

end PlanarFPP

end OAI
