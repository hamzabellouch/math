import OAI.Probability.FirstPassage.PositiveMoment
import OAI.Probability.FirstPassage.Reversal

namespace OAI

namespace PlanarFPP
open MeasureTheory ProbabilityTheory Finset
open scoped ENNReal

def straightEdge (p : Vertex) (d : Step) (i : ℕ) : Edge :=
  d.edge (p + (i : ℤ) • d.delta)

theorem straightEdge_injective (p : Vertex) (d : Step) :
    Function.Injective (straightEdge p d) := by
  intro i j h
  cases d <;> simp [straightEdge, Step.edge, Step.delta, Prod.ext_iff] at h <;> omega

theorem straightEdge_succ (p : Vertex) (d : Step) (i : ℕ) :
    straightEdge p d (i + 1) = straightEdge (p + d.delta) d i := by
  unfold straightEdge
  congr 1
  simp [Nat.cast_add, add_smul, add_comm, add_assoc]

theorem pathCost_replicate (w : Edge → ℝ) (p : Vertex) (d : Step) (n : ℕ) :
    pathCost w p (List.replicate n d) =
      ∑ i ∈ range n, w (straightEdge p d i) := by
  induction n generalizing p with
  | zero => simp [pathCost]
  | succ n ih =>
    rw [List.replicate_succ, pathCost, ih, sum_range_succ']
    simp [straightEdge, Nat.cast_add, add_smul, add_assoc, add_comm]

theorem pathCost_replicate_edgeSet (w : Edge → ℝ) (p : Vertex) (d : Step) (n : ℕ) :
    pathCost w p (List.replicate n d) =
      ∑ e ∈ (range n).image (straightEdge p d), w e := by
  rw [sum_image (fun i _ j _ hij => straightEdge_injective p d hij)]
  exact pathCost_replicate w p d n

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {τ : Edge → Ω → ℝ}

theorem costly_straight_probability (h : ExponentialEnvironment P τ)
    (p : Vertex) (d : Step) (n : ℕ) (t : ℝ) :
    P {ω | t ≤ pathCost (fun e => τ e ω) p (List.replicate n d)} ≤
      2 ^ n / ENNReal.ofReal (Real.exp (t / 2)) := by
  simp only [pathCost_replicate_edgeSet]
  have ht := costly_edge_set_probability h ((range n).image (straightEdge p d)) t
  simpa only [card_image_of_injective _ (straightEdge_injective p d), card_range] using ht

theorem costly_straight_probability_real (h : ExponentialEnvironment P τ)
    (p : Vertex) (d : Step) (n : ℕ) (t : ℝ) :
    P.real {ω | t ≤ pathCost (fun e => τ e ω) p (List.replicate n d)} ≤
      (2 : ℝ) ^ n * Real.exp (-t / 2) := by
  have hr := ENNReal.toReal_mono (show (2 : ℝ≥0∞)^n /
      ENNReal.ofReal (Real.exp (t/2)) ≠ ⊤ from
      ENNReal.div_ne_top (by simp) (by positivity))
    (costly_straight_probability h p d n t)
  simp only [ENNReal.toReal_div, ENNReal.toReal_pow,
    ENNReal.toReal_ofReal (Real.exp_pos _).le, ENNReal.toReal_ofNat] at hr
  change P.real _ ≤ _ at hr
  rw [show -t / 2 = -(t / 2) by ring, Real.exp_neg]
  simpa only [div_eq_mul_inv] using hr

theorem costly_straight_excess_probability_real (h : ExponentialEnvironment P τ)
    (p : Vertex) (d : Step) (n : ℕ) (t : ℝ) :
    P.real {ω | 4 * (n : ℝ) + t ≤
      pathCost (fun e => τ e ω) p (List.replicate n d)} ≤ Real.exp (-t / 2) := by
  refine (costly_straight_probability_real h p d n (4 * n + t)).trans ?_
  have htwo : (2 : ℝ) ≤ Real.exp 2 := by
    have := Real.add_one_le_exp (2 : ℝ)
    linarith
  have hp : (2 : ℝ)^n ≤ Real.exp (2 * (n : ℝ)) := by
    rw [mul_comm (2 : ℝ), Real.exp_nat_mul]
    exact pow_le_pow_left₀ (by norm_num) htwo n
  calc
    (2 : ℝ)^n * Real.exp (-(4 * n + t) / 2) ≤
        Real.exp (2 * (n : ℝ)) * Real.exp (-(4 * n + t) / 2) :=
      mul_le_mul_of_nonneg_right hp (Real.exp_pos _).le
    _ = Real.exp (-t / 2) := by rw [← Real.exp_add]; congr 1; ring

def coordinatePath (p q : Vertex) : List Step :=
  horizontal (q.1 - p.1) ++ vertical (q.2 - p.2)

def latticeDistance (p q : Vertex) : ℕ :=
  (q.1 - p.1).natAbs + (q.2 - p.2).natAbs

theorem coordinatePath_endpoint (p q : Vertex) : p + displacement (coordinatePath p q) = q := by
  simp [coordinatePath, displacement_horizontal, displacement_vertical, Prod.ext_iff]

theorem costly_horizontal_excess_probability_real (h : ExponentialEnvironment P τ)
    (p : Vertex) (a : ℤ) (t : ℝ) :
    P.real {ω | 4 * (a.natAbs : ℝ) + t ≤
      pathCost (fun e => τ e ω) p (horizontal a)} ≤ Real.exp (-t / 2) := by
  by_cases ha : 0 ≤ a
  · have he : a.toNat = a.natAbs := by omega
    simpa only [horizontal, ite_eq_left ha, he] using
      costly_straight_excess_probability_real h p Step.east a.toNat t
  · have he : (-a).toNat = a.natAbs := by omega
    simpa only [horizontal, ite_eq_right ha, he] using
      costly_straight_excess_probability_real h p Step.west (-a).toNat t

theorem costly_vertical_excess_probability_real (h : ExponentialEnvironment P τ)
    (p : Vertex) (a : ℤ) (t : ℝ) :
    P.real {ω | 4 * (a.natAbs : ℝ) + t ≤
      pathCost (fun e => τ e ω) p (vertical a)} ≤ Real.exp (-t / 2) := by
  by_cases ha : 0 ≤ a
  · have he : a.toNat = a.natAbs := by omega
    simpa only [vertical, ite_eq_left ha, he] using
      costly_straight_excess_probability_real h p Step.north a.toNat t
  · have he : (-a).toNat = a.natAbs := by omega
    simpa only [vertical, ite_eq_right ha, he] using
      costly_straight_excess_probability_real h p Step.south (-a).toNat t

theorem costly_coordinatePath_probability_real (h : ExponentialEnvironment P τ)
    (p q : Vertex) (t : ℝ) :
    P.real {ω | 4 * (latticeDistance p q : ℝ) + t ≤
      pathCost (fun e => τ e ω) p (coordinatePath p q)} ≤ 2 * Real.exp (-t / 4) := by
  let _ := h.probability
  let A := {ω | 4 * ((q.1-p.1).natAbs : ℝ) + t/2 ≤
    pathCost (fun e => τ e ω) p (horizontal (q.1-p.1))}
  let B := {ω | 4 * ((q.2-p.2).natAbs : ℝ) + t/2 ≤
    pathCost (fun e => τ e ω) (p + displacement (horizontal (q.1-p.1)))
      (vertical (q.2-p.2))}
  have hs : {ω | 4 * (latticeDistance p q : ℝ) + t ≤
      pathCost (fun e => τ e ω) p (coordinatePath p q)} ⊆ A ∪ B := by
    intro ω hω
    change _ ∨ _
    by_contra hn
    push Not at hn
    simp only [Set.mem_ofPred_eq, coordinatePath, pathCost_append, latticeDistance, Nat.cast_add] at hω
    simp only [A, B, Set.mem_ofPred_eq, not_le] at hn
    linarith
  refine (measureReal_mono hs).trans ((measureReal_union_le A B).trans ?_)
  have ha := costly_horizontal_excess_probability_real h p (q.1-p.1) (t/2)
  have hb := costly_vertical_excess_probability_real h
    (p + displacement (horizontal (q.1-p.1))) (q.2-p.2) (t/2)
  change P.real A + P.real B ≤ _
  change P.real A ≤ _ at ha
  change P.real B ≤ _ at hb
  have he : -(t / 2) / 2 = -t / 4 := by ring
  rw [he] at ha hb
  linarith

end PlanarFPP

end OAI
