import OAI.NumberTheory.Jacobsthal.Paths.ActualThresholdArrival

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.CanonicalMarkSlack

open _root_.Set _root_.Filter _root_.MeasureTheory ProbabilityTheory
open FinitePathMeasures FinitePathGeometry ArrivalKernelGeometry RegeneratingInverseBands
open CanonicalCostCoordinates Erdos970Dependency.MarkedVisits

theorem firstArrivalMark_bounds (z : CostState) (hz : firstArrivalMark z = true) :
    stateSide z.1 = .even ∧ 209/100 ≤ stateRatio z.1 ∧ stateRatio z.1 ≤ 213/100 := by
  rcases z with ⟨s,T⟩
  cases s with
  | inl s =>
    have h := (sourceMark_true s).mp hz
    exact ⟨rfl,h.1,h.2⟩
  | inr s => exact Bool.noConfusion hz

theorem pair_hit_slack {r b₀ b₁ : ℝ} (hr : 0 < r) (hb₀ : 0 < b₀) (hb₁ : 0 < b₁)
    (a k N : ℕ) (hk : a+2*k+1 ≤ N) (h : RawHistory N)
    (htime : (h ⟨a+2*k+1,Finset.mem_Iic.mpr hk⟩).2 =
      (h ⟨a+2*k,Finset.mem_Iic.mpr (by omega)⟩).2 +
        cost (stateRatio (h ⟨a+2*k+1,Finset.mem_Iic.mpr hk⟩).1))
    (hHit : h ∈ pairHitTest a k N hk (Real.log (r/b₁)) (Real.log (b₁/(10*b₀)))) :
    let z := h ⟨a+2*k+1,Finset.mem_Iic.mpr hk⟩
    stateSide z.1 = .even ∧ 209/100 ≤ stateRatio z.1 ∧ stateRatio z.1 ≤ 213/100 ∧
      10*b₀/(313/100) ≤ currentExponent (Real.log r) z ∧
      currentExponent (Real.log r) z ≤ b₁/(309/100) ∧ 6*b₀ < gapValue (Real.log r) z := by
  dsimp only
  let pre := h ⟨a+2*k,Finset.mem_Iic.mpr (show a+2*k ≤ N by omega)⟩
  let z := h ⟨a+2*k+1,Finset.mem_Iic.mpr hk⟩
  have hmark := firstArrivalMark_bounds z hHit.2.1
  have hwindow := (marked_cost_window hr hb₀ hb₁ pre.2).mpr hHit.2.2
  have hslack := marked_draw_slack hb₀ hwindow.1 hwindow.2 hmark.2.1 hmark.2.2
  have hz : z = (z.1,pre.2+cost (stateRatio z.1)) := Prod.ext rfl htime
  have he : currentExponent (Real.log r) z = nextExponent (gapAt r pre.2) (stateRatio z.1) := by
    calc
      _ = currentExponent (Real.log r) (z.1,pre.2+cost (stateRatio z.1)) := congrArg _ hz
      _ = nextExponent (gapValue (Real.log r) pre) (stateRatio z.1) := currentExponent_update _ pre z.1
      _ = _ := by rw [gapValue_log_eq_gapAt hr]
  have hg : gapValue (Real.log r) z = nextGap (gapAt r pre.2) (stateRatio z.1) := by
    calc
      _ = gapValue (Real.log r) (z.1,pre.2+cost (stateRatio z.1)) := congrArg _ hz
      _ = nextGap (gapValue (Real.log r) pre) (stateRatio z.1) := gapValue_update _ pre z.1
      _ = _ := by rw [gapValue_log_eq_gapAt hr]
  exact ⟨hmark.1,hmark.2.1,hmark.2.2,he ▸ hslack.1,he ▸ hslack.2.1,hg ▸ hslack.2.2.2.2.1⟩

theorem canonical_all_marks_slack {r b₀ b₁ : ℝ} (hr : 0 < r) (hb₀ : 0 < b₀) (hb₁ : 0 < b₁)
    (s : State) (N : ℕ) :
    ∀ᵐ h ∂finitePathMeasure s N, ∀ a k : ℕ, ∀ hk : a+2*k+1 ≤ N,
      h ∈ pairHitTest a k N hk (Real.log (r/b₁)) (Real.log (b₁/(10*b₀))) →
      let z := h ⟨a+2*k+1,Finset.mem_Iic.mpr hk⟩
      stateSide z.1 = .even ∧ 209/100 ≤ stateRatio z.1 ∧ stateRatio z.1 ≤ 213/100 ∧
        10*b₀/(313/100) ≤ currentExponent (Real.log r) z ∧
        currentExponent (Real.log r) z ≤ b₁/(309/100) ∧ 6*b₀ < gapValue (Real.log r) z := by
  have hall : ∀ᵐ h ∂finitePathMeasure s N, ∀ j : Fin N,
      (h ⟨j.1+1,Finset.mem_Iic.mpr (by have := j.isLt; omega)⟩).2 =
        (h ⟨j.1,Finset.mem_Iic.mpr j.isLt.le⟩).2 +
          cost (stateRatio (h ⟨j.1+1,Finset.mem_Iic.mpr (by have := j.isLt; omega)⟩).1) := by
    apply ae_all_iff.mpr
    intro j
    exact raw_cost_coordinate (Nat.zero_le _) j.isLt (fun _ => (s,0))
  filter_upwards [hall] with h hh
  intro a k hk hHit
  exact pair_hit_slack hr hb₀ hb₁ a k N hk h
    (hh ⟨a+2*k,by omega⟩) hHit

end NumberTheoryLean.CanonicalMarkSlack

end

section

namespace NumberTheoryLean.CompletedMarkEvents

open _root_.Set _root_.MeasureTheory ProbabilityTheory
open FinitePathGeometry FinitePathMeasures FiniteHistoryTransport CemeteryKernel
open ArrivalKernelGeometry RegeneratingInverseBands ActualCouplingUpdates

def strongMark (v b₀ b₁ : ℝ) (z : CostState) : Prop :=
  stateSide z.1 = .even ∧ 209/100 ≤ stateRatio z.1 ∧ stateRatio z.1 ≤ 213/100 ∧
    10*b₀/(313/100) ≤ currentExponent v z ∧ currentExponent v z ≤ b₁/(309/100)

theorem strongMark_measurable (v b₀ b₁ : ℝ) : MeasurableSet {z | strongMark v b₀ b₁ z} :=
  (measurable_fst (side_set_measurable .even)).inter
    ((measurableSet_le measurable_const (stateRatio_measurable.comp measurable_fst)).inter
      ((measurableSet_le (stateRatio_measurable.comp measurable_fst) measurable_const).inter
        ((measurableSet_le measurable_const (currentExponent_measurable v)).inter
          (measurableSet_le (currentExponent_measurable v) measurable_const))))

def markedPoint (v b₀ b₁ : ℝ) : Space CostState → Prop :=
  Sum.elim (strongMark v b₀ b₁) (fun _ => False)

def compactPoint (v R : ℝ) : Space CostState → Prop :=
  Sum.elim (fun z => gapValue v z ≤ R) (fun _ => False)

theorem markedPoint_measurable (v b₀ b₁ : ℝ) : MeasurableSet {z | markedPoint v b₀ b₁ z} :=
  measurableSet_sum_iff.mpr ⟨strongMark_measurable _ _ _,MeasurableSet.empty⟩

theorem compactPoint_measurable (v R : ℝ) : MeasurableSet {z | compactPoint v R z} :=
  measurableSet_sum_iff.mpr ⟨measurableSet_le (gapValue_measurable v) measurable_const,MeasurableSet.empty⟩

def noStrongBefore (v b₀ b₁ : ℝ) (N k : ℕ) (h : Hist (Space CostState) N) : Prop :=
  ∀ i : Finset.Iic N,i.1 ≤ k → ¬markedPoint v b₀ b₁ (h i)

theorem noStrongBefore_measurable (v b₀ b₁ : ℝ) (N k : ℕ) :
    MeasurableSet {h | noStrongBefore v b₀ b₁ N k h} := by
  simp only [noStrongBefore,Set.ofPred_forall]
  apply MeasurableSet.iInter
  intro i
  apply MeasurableSet.iInter
  intro _hi
  exact ((measurable_pi_apply i) (markedPoint_measurable v b₀ b₁)).compl

def badCompactPath (v R b₀ b₁ : ℝ) (N : ℕ) : Set (Hist (Space CostState) N) :=
  {h | ∃ j : Finset.Iic N,compactPoint v R (h j) ∧ noStrongBefore v b₀ b₁ N j.1 h}

theorem badCompactPath_measurable (v R b₀ b₁ : ℝ) (N : ℕ) :
    MeasurableSet (badCompactPath v R b₀ b₁ N) := by
  simp only [badCompactPath,Set.ofPred_exists]
  apply MeasurableSet.iUnion
  intro j
  exact ((measurable_pi_apply j) (compactPoint_measurable v R)).inter
    (noStrongBefore_measurable v b₀ b₁ N j.1)

end NumberTheoryLean.CompletedMarkEvents

end

end Erdos970

end OAI
