import OAI.Probability.GammaPassage.CoordinateTails

namespace OAI

namespace GammaFPP
open PlanarFPP MeasureTheory ProbabilityTheory Set

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
variable {τ : Edge → Ω → ℝ} {shape rate : ℝ}

/-- Combined attachment cost for a real distance budget, without an
independence assumption between the attachments. -/
theorem GammaEnvironment.two_attachment_cost_probability
    (h : GammaEnvironment shape rate P τ) (hs : 0 < shape) (hr : 0 < rate)
    (p p' q' q : Vertex) (L t : ℝ)
    (hdist : (latticeDistance p p' : ℝ) + (latticeDistance q' q : ℝ) ≤ L) :
    P.real {ω | coordinateAllowance shape rate * L + t ≤
      pathCost (fun e => τ e ω) p (coordinatePath p p') +
      pathCost (fun e => τ e ω) q' (coordinatePath q' q)} ≤
      4 * Real.exp (-(rate / 8) * t) := by
  let := h.probability
  let A := {ω | coordinateAllowance shape rate * (latticeDistance p p' : ℝ) + t/2 ≤
    pathCost (fun e => τ e ω) p (coordinatePath p p')}
  let B := {ω | coordinateAllowance shape rate * (latticeDistance q' q : ℝ) + t/2 ≤
    pathCost (fun e => τ e ω) q' (coordinatePath q' q)}
  have hdist' := mul_le_mul_of_nonneg_left hdist (coordinateAllowance_pos hs hr).le
  have hsub : {ω | coordinateAllowance shape rate * L + t ≤
      pathCost (fun e => τ e ω) p (coordinatePath p p') +
      pathCost (fun e => τ e ω) q' (coordinatePath q' q)} ⊆ A ∪ B := by
    intro ω hω
    change _ ∨ _
    by_contra hn
    push Not at hn
    simp only [A, B, mem_ofPred_eq, not_le] at hn
    simp only [mem_ofPred_eq] at hω
    nlinarith
  refine (measureReal_mono hsub).trans ((measureReal_union_le A B).trans ?_)
  have ha := h.costly_coordinatePath_probability_real hs hr p p' (t/2)
  have hb := h.costly_coordinatePath_probability_real hs hr q' q (t/2)
  change P.real A ≤ _ at ha
  change P.real B ≤ _ at hb
  have he : -(rate/4)*(t/2) = -(rate/8)*t := by ring
  rw [he] at ha hb
  change P.real A + P.real B ≤ _
  linarith

/-- A finite-net attachment allowance exists for every positive Gamma law
and every norm Lipschitz constant. -/
theorem endpoint_net_budget (hs : 0 < shape) (hr : 0 < rate)
    (β η δ : ℝ) (hβ : 0 ≤ β) (hη : 0 < η) (hδ : 0 < δ) :
    ∃ γ : ℝ, 0 < γ ∧
      (4 * coordinateAllowance shape rate + 2*β)*γ ≤ η/2 ∧ γ ≤ δ/12 := by
  let C := 4 * coordinateAllowance shape rate + 2*β
  have hC : 0 < C := by
    dsimp [C]
    have := coordinateAllowance_pos hs hr
    positivity
  refine ⟨min (η/(2*C)) (δ/12), lt_min (by positivity) (by positivity), ?_, min_le_right _ _⟩
  have hh : min (η/(2*C)) (δ/12) ≤ η/(2*C) := min_le_left _ _
  have hb := (le_div_iff₀ (by positivity : 0 < 2*C)).mp hh
  change C * min (η/(2*C)) (δ/12) ≤ η/2
  nlinarith

end GammaFPP

end OAI
