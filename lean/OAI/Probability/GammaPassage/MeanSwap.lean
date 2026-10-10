import OAI.Probability.GammaPassage.MeanLimit

namespace OAI

namespace GammaFPP
open MeasureTheory ProbabilityTheory Filter Topology PlanarFPP

namespace SwapGeometry

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

end SwapGeometry

variable {Ω : Type*} [MeasurableSpace Ω]
variable {P : Measure Ω} {τ : Edge → Ω → ℝ} {ν : Measure ℝ}

/-- The actual undirected edge swap is a bijection, not just a sign reversal. -/
def swapEdgeEquiv : Edge ≃ Edge where
  toFun := SwapGeometry.swapEdge
  invFun := SwapGeometry.swapEdge
  left_inv := SwapGeometry.swapEdge_swap
  right_inv := SwapGeometry.swapEdge_swap

theorem IidEnvironment.coordinateSwap (h : IidEnvironment ν P τ) :
    IidEnvironment ν P (fun e => τ (SwapGeometry.swapEdge e)) where
  probability := h.probability
  measurable := fun e => h.measurable (SwapGeometry.swapEdge e)
  independent := h.independent.precomp SwapGeometry.swapEdge_injective
  marginal := fun e => h.marginal (SwapGeometry.swapEdge e)

/-- Equality of full configuration measures, not merely finite marginals. -/
theorem IidEnvironment.coordinateSwap_jointLaw (h : IidEnvironment ν P τ) :
    Measure.map (fun ω e => τ (SwapGeometry.swapEdge e) ω) P =
      Measure.map (fun ω e => τ e ω) P :=
  h.coordinateSwap.jointLaw.trans h.jointLaw.symm

/-- Coordinate swap preserves the integral of each passage time; the integral
identity also holds for the totalized integral without an integrability assumption. -/
theorem IidEnvironment.integral_passageTime_coordinateSwap
    (h : IidEnvironment ν P τ) (p q : Vertex) :
    (∫ ω, passageTime (fun e => τ e ω) p.swap q.swap ∂P) =
      ∫ ω, passageTime (fun e => τ e ω) p q ∂P := by
  have hm : Measurable (fun w : Edge → ℝ => passageTime w p q) :=
    PlanarFPP.measurable_passageTime (fun e => measurable_pi_apply e) p q
  have hs := h.coordinateSwap.integral_configuration
    (fun w : Edge → ℝ => passageTime w p q) hm
  have ho := h.integral_configuration
    (fun w : Edge → ℝ => passageTime w p q) hm
  have he : (∫ ω, passageTime (fun e => τ e ω) p.swap q.swap ∂P) =
      ∫ ω, passageTime (fun e => τ (SwapGeometry.swapEdge e) ω) p q ∂P :=
    integral_congr_ae (Filter.Eventually.of_forall fun ω =>
      SwapGeometry.passageTime_swap (fun e => τ e ω) p q)
  exact he.trans (hs.trans ho.symm)

variable {shape rate : ℝ}

/-- The equality holds for every index including zero, and swaps the two
coordinates rather than applying central symmetry. -/
theorem GammaEnvironment.meanPassageSequence_coordinateSwap
    (h : GammaEnvironment shape rate P τ) (z : Vertex) (n : ℕ) :
    meanPassageSequence P τ z.swap n = meanPassageSequence P τ z n := by
  have he : (n • z).swap = n • z.swap := rfl
  have hz : (0 : Vertex).swap = 0 := rfl
  simpa only [meanPassageSequence, he, hz] using
    h.integral_passageTime_coordinateSwap 0 (n • z)

/-- Actual deterministic mean-limit invariance, with no norm or time-constant
existence premise. It also includes the zero direction. -/
theorem GammaEnvironment.directionalMeanConstant_coordinateSwap
    (h : GammaEnvironment shape rate P τ) (hs : 0 < shape) (hr : 0 < rate)
    (z : Vertex) :
    directionalMeanConstant h hs hr z.swap = directionalMeanConstant h hs hr z := by
  have ht := h.meanPassageSequence_tendsto hs hr z.swap
  simp only [h.meanPassageSequence_coordinateSwap] at ht
  exact tendsto_nhds_unique ht (h.meanPassageSequence_tendsto hs hr z)

end GammaFPP

end OAI
