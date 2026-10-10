import OAI.Probability.GammaPassage.FiniteTails
import OAI.Probability.FirstPassage.CoordinateTails
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace OAI

namespace GammaFPP
open MeasureTheory ProbabilityTheory PlanarFPP Finset
open scoped ENNReal

variable {Ω : Type*} [MeasurableSpace Ω]
variable {P : Measure Ω} {τ : Edge → Ω → ℝ} {shape rate : ℝ}

/-- A linear allowance depending on the Gamma shape and rate. -/
noncomputable def coordinateAllowance (shape rate : ℝ) : ℝ := 2 * (shape + 1) / rate

lemma coordinateAllowance_pos (hs : 0 < shape) (hr : 0 < rate) :
    0 < coordinateAllowance shape rate := by
  unfold coordinateAllowance
  positivity

/-- Exponential upper tail for the cost of a straight lattice path. -/
theorem GammaEnvironment.costly_straight_probability
    (h : GammaEnvironment shape rate P τ) (hs : 0 < shape) (hr : 0 < rate)
    (p : Vertex) (d : Step) (n : ℕ) (t : ℝ) :
    P {ω | t ≤ pathCost (fun e => τ e ω) p (List.replicate n d)} ≤
      (ENNReal.ofReal ((2 : ℝ) ^ shape)) ^ n /
        ENNReal.ofReal (Real.exp ((rate / 2) * t)) := by
  have hp : 0 < rate / 2 := by positivity
  have hl : rate / 2 < rate := by linarith
  have he : rate / (rate - rate / 2) = 2 := by
    have hd : rate - rate / 2 ≠ 0 := (sub_pos.mpr hl).ne'
    field_simp [hd]; ring
  have hb := h.upper_tail_edgeSum hs hr hp hl
    ((range n).image (straightEdge p d)) t
  simpa only [edgeSum, pathCost_replicate_edgeSet, he,
    card_image_of_injective _ (straightEdge_injective p d), card_range] using hb

/-- The real-valued upper tail for the cost of a straight lattice path. -/
theorem GammaEnvironment.costly_straight_probability_real
    (h : GammaEnvironment shape rate P τ) (hs : 0 < shape) (hr : 0 < rate)
    (p : Vertex) (d : Step) (n : ℕ) (t : ℝ) :
    P.real {ω | t ≤ pathCost (fun e => τ e ω) p (List.replicate n d)} ≤
      ((2 : ℝ) ^ shape) ^ n * Real.exp (-(rate / 2) * t) := by
  have hbase : 0 ≤ (2 : ℝ) ^ shape := (Real.rpow_pos_of_pos (by norm_num) shape).le
  have hden : ENNReal.ofReal (Real.exp ((rate / 2) * t)) ≠ 0 :=
    ENNReal.ofReal_ne_zero_iff.mpr (Real.exp_pos _)
  have hn : (ENNReal.ofReal ((2 : ℝ) ^ shape)) ^ n /
      ENNReal.ofReal (Real.exp ((rate / 2) * t)) ≠ ⊤ :=
    ENNReal.div_ne_top (ENNReal.pow_ne_top ENNReal.ofReal_ne_top) hden
  have hb := ENNReal.toReal_mono hn (h.costly_straight_probability hs hr p d n t)
  simp only [ENNReal.toReal_div, ENNReal.toReal_pow,
    ENNReal.toReal_ofReal hbase, ENNReal.toReal_ofReal (Real.exp_pos _).le] at hb
  change P.real _ ≤ _ at hb
  rw [show -(rate / 2) * t = -((rate / 2) * t) by ring, Real.exp_neg]
  simpa only [div_eq_mul_inv] using hb

lemma gamma_half_rate_mgf_bound (hs : 0 < shape) :
    (2 : ℝ) ^ shape ≤ Real.exp (shape + 1) := by
  rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
  apply Real.exp_le_exp.mpr
  have hl : Real.log (2 : ℝ) ≤ 1 := by
    have hb := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at hb ⊢
    exact hb
  nlinarith

/-- Exponential tail above the linear allowance, for every real excess `t`. -/
theorem GammaEnvironment.costly_straight_excess_probability_real
    (h : GammaEnvironment shape rate P τ) (hs : 0 < shape) (hr : 0 < rate)
    (p : Vertex) (d : Step) (n : ℕ) (t : ℝ) :
    P.real {ω | coordinateAllowance shape rate * (n : ℝ) + t ≤
      pathCost (fun e => τ e ω) p (List.replicate n d)} ≤
      Real.exp (-(rate / 2) * t) := by
  refine (h.costly_straight_probability_real hs hr p d n
    (coordinateAllowance shape rate * n + t)).trans ?_
  have hp : ((2 : ℝ) ^ shape) ^ n ≤ Real.exp ((n : ℝ) * (shape + 1)) := by
    rw [Real.exp_nat_mul]
    exact pow_le_pow_left₀ (Real.rpow_pos_of_pos (by norm_num) shape).le
      (gamma_half_rate_mgf_bound hs) n
  calc
    ((2 : ℝ) ^ shape) ^ n *
        Real.exp (-(rate / 2) * (coordinateAllowance shape rate * n + t)) ≤
        Real.exp ((n : ℝ) * (shape + 1)) *
          Real.exp (-(rate / 2) * (coordinateAllowance shape rate * n + t)) :=
      mul_le_mul_of_nonneg_right hp (Real.exp_pos _).le
    _ = Real.exp (-(rate / 2) * t) := by
      rw [← Real.exp_add]
      congr 1
      unfold coordinateAllowance
      field_simp [hr.ne']; ring

theorem GammaEnvironment.costly_horizontal_excess_probability_real
    (h : GammaEnvironment shape rate P τ) (hs : 0 < shape) (hr : 0 < rate)
    (p : Vertex) (a : ℤ) (t : ℝ) :
    P.real {ω | coordinateAllowance shape rate * (a.natAbs : ℝ) + t ≤
      pathCost (fun e => τ e ω) p (horizontal a)} ≤ Real.exp (-(rate / 2) * t) := by
  by_cases ha : 0 ≤ a
  · have he : a.toNat = a.natAbs := by omega
    simpa only [horizontal, ite_eq_left ha, he] using
      h.costly_straight_excess_probability_real hs hr p Step.east a.toNat t
  · have he : (-a).toNat = a.natAbs := by omega
    simpa only [horizontal, ite_eq_right ha, he] using
      h.costly_straight_excess_probability_real hs hr p Step.west (-a).toNat t

theorem GammaEnvironment.costly_vertical_excess_probability_real
    (h : GammaEnvironment shape rate P τ) (hs : 0 < shape) (hr : 0 < rate)
    (p : Vertex) (a : ℤ) (t : ℝ) :
    P.real {ω | coordinateAllowance shape rate * (a.natAbs : ℝ) + t ≤
      pathCost (fun e => τ e ω) p (vertical a)} ≤ Real.exp (-(rate / 2) * t) := by
  by_cases ha : 0 ≤ a
  · have he : a.toNat = a.natAbs := by omega
    simpa only [vertical, ite_eq_left ha, he] using
      h.costly_straight_excess_probability_real hs hr p Step.north a.toNat t
  · have he : (-a).toNat = a.natAbs := by omega
    simpa only [vertical, ite_eq_right ha, he] using
      h.costly_straight_excess_probability_real hs hr p Step.south (-a).toNat t

/-- A union bound for the two coordinate legs, counting every edge traversal. -/
theorem GammaEnvironment.costly_coordinatePath_probability_real
    (h : GammaEnvironment shape rate P τ) (hs : 0 < shape) (hr : 0 < rate)
    (p q : Vertex) (t : ℝ) :
    P.real {ω | coordinateAllowance shape rate * (latticeDistance p q : ℝ) + t ≤
      pathCost (fun e => τ e ω) p (coordinatePath p q)} ≤
      2 * Real.exp (-(rate / 4) * t) := by
  let := h.probability
  let A := {ω | coordinateAllowance shape rate * ((q.1-p.1).natAbs : ℝ) + t/2 ≤
    pathCost (fun e => τ e ω) p (horizontal (q.1-p.1))}
  let B := {ω | coordinateAllowance shape rate * ((q.2-p.2).natAbs : ℝ) + t/2 ≤
    pathCost (fun e => τ e ω) (p + displacement (horizontal (q.1-p.1)))
      (vertical (q.2-p.2))}
  have hsub : {ω | coordinateAllowance shape rate * (latticeDistance p q : ℝ) + t ≤
      pathCost (fun e => τ e ω) p (coordinatePath p q)} ⊆ A ∪ B := by
    intro ω hω
    change _ ∨ _
    by_contra hn
    push Not at hn
    simp only [Set.mem_ofPred_eq, coordinatePath, pathCost_append, latticeDistance,
      Nat.cast_add] at hω
    simp only [A, B, Set.mem_ofPred_eq, not_le] at hn
    linarith
  refine (measureReal_mono hsub).trans ((measureReal_union_le A B).trans ?_)
  have ha := h.costly_horizontal_excess_probability_real hs hr p (q.1-p.1) (t/2)
  have hb := h.costly_vertical_excess_probability_real hs hr
    (p + displacement (horizontal (q.1-p.1))) (q.2-p.2) (t/2)
  change P.real A + P.real B ≤ _
  change P.real A ≤ _ at ha
  change P.real B ≤ _ at hb
  have he : -(rate / 2) * (t / 2) = -(rate / 4) * t := by ring
  rw [he] at ha hb
  linarith

end GammaFPP

end OAI
