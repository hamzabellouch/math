import OAI.Combinatorics.BalancedRyser.Selection.SelectionHistoryFinalLaw
import OAI.Combinatorics.BalancedRyser.Selection.SelectionOccupancyTail
import OAI.Combinatorics.BalancedRyser.Selection.SelectionProcessScales

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Preorder
open scoped MeasureTheory ProbabilityTheory BigOperators

namespace Balanced.Selection.Process
attribute [local instance] Classical.propDecidable
variable {I V P D L : Type*} [Fintype I] [Fintype V]
  [Fintype P] [Fintype D] [Fintype L]

theorem sourceTerminalLaw_agrees_recorded [Nonempty V]
    (p : Parameters) (q : ℕ) (G : Input I V)
    (hno : ∀ v w, G.slot v = G.slot w → ¬ G.graph.Adj v w)
    (S : State I V) (a : I → V)
    (hpos : 0 < (sourceTerminalLaw p q G hno S).weight a) :
    ∀ i, i ∉ S.remaining → S.recorded i = some (a i) := by
  unfold sourceTerminalLaw at hpos
  split at hpos
  · unfold terminalLaw at hpos
    split at hpos
    next h =>
      change 0 < ((PMF.uniformOfFinset (Tail.successfulAssignments G S) _).map
        (Tail.complete G S (recordedAssignment S)) a).toReal at hpos
      have hs := (PMF.apply_pos_iff _ _).mp (ENNReal.toReal_pos_iff.mp hpos).1
      obtain ⟨b, _, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hs
      exact Tail.complete_agrees_recorded G S (recordedAssignment S)
        (recordedAssignment_recorded G S h.1) b
    next => simp [failureLaw] at hpos
  · simp [failureLaw] at hpos

theorem finalLaw_occupancy_bound [Nonempty V] (p : Parameters) (hp : p.Admissible)
    (q : ℕ) (hq : 2 ≤ q) (hPq : 2 * p.Pstar ≤ q) (hBq : 2 * p.Bstar ≤ q)
    (hρq : 2 ≤ p.rho * q) (G : Input I V)
    (hn : Fintype.card I = 2 * (q + 1))
    (hno : ∀ v w, G.slot v = G.slot w → ¬ G.graph.Adj v w)
    (A : FiniteAffine.Plane q P D L) (index : I ≃ D × Bool) (line : V → L)
    (hline : Selection.LineAssignment G A index line) (T : L → Finset P)
    (hT : Selection.TrackedSets A T p.c₀) :
    Selection.occupancyFailureMass (finalLaw p q G hno) A line T p.rho ≤
      2 * (q : ℝ) * (q + 1) * Real.exp (-p.occupancyDecay * q) := by
  let N := p.lastMainTime q (Fintype.card I)
  let bad : Option (State I V) → Prop := fun out => ∃ S, out = some S ∧ ∃ l,
    ((recordedTracked q A line T S l).card : ℝ) ≤ 2 * p.rho * q
  have hpoints : ∀ l x, x ∈ T l → A.incident x l := by
    intro l x hx
    exact (Finset.mem_filter.mp ((hT l).1 hx)).2
  have hcard : ∀ l, p.c₀ * q ≤ ((T l).card : ℝ) := fun l => (hT l).2
  have htime : N ≤ 3 * q := by
    have hN : N ≤ Fintype.card I := Nat.sub_le _ _
    omega
  have hbound := surviving_recorded_occupancy_bound p hp q (by omega) hPq hBq
    G A index line hline T hpoints hcard N htime
  change (snapshotPathLaw p q G).real {ω | (ω N).1 ∈ {o | bad o}} ≤ _ at hbound
  rw [state_event_real_eq_historyWeight] at hbound
  refine le_trans ?_ hbound
  rw [occupancyFailureMass_finalLaw]
  apply Finset.sum_le_sum
  intro out _
  have hw := historyWeight_nonnegative p q G N out
  change historyWeight p q G N out * _ ≤ _
  by_cases hzero : historyWeight p q G N out = 0
  · simp [hzero]
  have hpos : 0 < historyWeight p q G N out := lt_of_le_of_ne hw (Ne.symm hzero)
  cases out with
  | none => simp [sourceTerminalOutcomeLaw, Selection.occupancyFailureMass, failureLaw, bad]
  | some S =>
    have htail : p.tailSlots q ≤ Fintype.card I := by
      have ht := Parameters.tailSlots_le_order hp q
      omega
    have hrem : S.remaining.card = p.tailSlots q := by
      have hc := positive_historyWeight_card p q G N S hpos
      dsimp [N, Parameters.lastMainTime] at hc
      omega
    have hremR : (S.remaining.card : ℝ) ≤ p.rho * q := by
      rw [hrem]
      exact Parameters.tailSlots_le_rho_mul hp hρq
    have ht := completion_occupancyMass_le_bad_recorded p q G A line T hpoints S
      (sourceTerminalLaw p q G hno S) hremR
      (sourceTerminalLaw_agrees_recorded p q G hno S)
    have hm := mul_le_mul_of_nonneg_left ht hw
    simpa [bad, sourceTerminalOutcomeLaw, mul_ite] using hm

theorem outputLaw_occupancy_bound (p : Parameters) (hp : p.Admissible)
    (q : ℕ) (hq : 2 ≤ q) (hPq : 2 * p.Pstar ≤ q) (hBq : 2 * p.Bstar ≤ q)
    (hρq : 2 ≤ p.rho * q) (G : Input I V) (hG : GraphBounds G q p.c p.C)
    (A : FiniteAffine.Plane q P D L) (index : I ≃ D × Bool) (line : V → L)
    (hline : Selection.LineAssignment G A index line) (T : L → Finset P)
    (hT : Selection.TrackedSets A T p.c₀) :
    Selection.occupancyFailureMass (outputLaw p q G hG.2.1) A line T p.rho ≤
      2 * (q : ℝ) * (q + 1) * Real.exp (-p.occupancyDecay * q) := by
  let : Nonempty V := graphBounds_vertex_nonempty G q p.c p.C hp.1 (by omega) hG
  rw [outputLaw_eq_finalLaw]
  exact finalLaw_occupancy_bound p hp q hq hPq hBq hρq G hG.1 hG.2.1 A index line hline T hT

theorem eventually_outputLaw_occupancy_bound.{u, v, w}
    (p : Parameters) (hp : p.Admissible) :
    ∀ᶠ q : ℕ in atTop,
      ∀ (I : Type u) (V : Type v) [Fintype I] [Fintype V],
      ∀ G : Input I V, ∀ hG : GraphBounds G q p.c p.C,
      ∀ (P D L : Type w) [Fintype P] [Fintype D] [Fintype L],
      ∀ (A : FiniteAffine.Plane q P D L) (index : I ≃ D × Bool) (line : V → L),
      Selection.LineAssignment G A index line →
      ∀ T : L → Finset P, Selection.TrackedSets A T p.c₀ →
        Selection.occupancyFailureMass (outputLaw p q G hG.2.1) A line T p.rho ≤
          2 * (q : ℝ) * (q + 1) * Real.exp (-p.occupancyDecay * q) := by
  filter_upwards [Parameters.eventually_scale_regime p,
    Parameters.eventually_occupancy_regime hp] with q hs ho
  intro I V _ _ G hG P D L _ _ _ A index line hline T hT
  exact outputLaw_occupancy_bound p hp q hs.1 hs.2 ho.2.1 ho.2.2 G hG
    A index line hline T hT

end Balanced.Selection.Process

end

end OAI
