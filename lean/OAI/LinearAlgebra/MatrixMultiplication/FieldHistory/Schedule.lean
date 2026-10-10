import OAI.LinearAlgebra.MatrixMultiplication.FieldHistory.Populations

namespace OAI

/-! Finite extraction histories, inherited masks and recovery bounds. -/

noncomputable section

namespace MatrixMultiplication.AllFieldHistory

open AllFieldParameters
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq

def initialAncestor {K : ℕ} : CanonicalHistory K → Initial K
  | .initial h => h
  | .afterA h => h.1.val
  | .afterB h => h.1.val.1.val
  | .partC h => h.1.val.1.val.1.val
  | .afterC h => h.1.1.val.1.val.1.val

def ancestrySplits {K : ℕ} : CanonicalHistory K → List (Shape × Bool)
  | .initial _ => []
  | .afterA h => [(aSplit h, h.2.2)]
  | .afterB h => [(aSplit h.1.val, h.1.val.2.2), (bSplit h, h.2.2)]
  | .partC h => [(aSplit h.1.val.1.val, h.1.val.1.val.2.2),
      (bSplit h.1.val, h.1.val.2.2)]
  | .afterC h => [(aSplit h.1.1.val.1.val, h.1.1.val.1.val.2.2),
      (bSplit h.1.1.val, h.1.1.val.2.2), (cSplit h, h.2.2)]

def ancestrySubdivisions {K : ℕ} : CanonicalHistory K → List ℕ
  | .initial _ | .afterA _ | .afterB _ => []
  | .partC h => [h.2.val]
  | .afterC h => [h.1.2.val]

def historyKey {K : ℕ} (h : History K) : JointPopulation.HistoryKey where
  lot := (initialAncestor h.1).1.val
  initialShape := initialShape (initialAncestor h.1)
  physicalPlacement := h.2
  parentSplits := ancestrySplits h.1
  subdivisions := ancestrySubdivisions h.1

theorem placement_preserved {K : ℕ} (h : CanonicalHistory K) (phi psi : Placement)
    (heq : historyKey (h, phi) = historyKey (h, psi)) : phi = psi :=
  congrArg JointPopulation.HistoryKey.physicalPlacement heq

inductive Work (K : ℕ) where
  | stageA (h : InitialPositive K)
  | stageB (h : APositive K)
  | stageC (h : PartC K)
  deriving Fintype

def Work.source {K : ℕ} : Work K → CanonicalHistory K
  | .stageA h => .initial h.val
  | .stageB h => .afterA h.val
  | .stageC h => .partC h

def Work.stage {K : ℕ} : Work K → Fin 3
  | .stageA _ => 0
  | .stageB _ => 1
  | .stageC _ => 2

def Work.lot {K : ℕ} (w : Work K) : Fin K := (initialAncestor w.source).1

def Work.halfLength {K : ℕ} : Work K → ℕ
  | .stageA _ => 4
  | .stageB _ => 2
  | .stageC _ => 1

def Work.parentShape {K : ℕ} : Work K → Shape
  | .stageA h => initialShape h.val
  | .stageB h => aShape h.val
  | .stageC h => cShapeParent h

def Work.Branch {K : ℕ} : Work K → Type
  | .stageA h => ASplit h
  | .stageB h => BSplit h
  | .stageC _ => Fin 4

instance {K : ℕ} (w : Work K) : Fintype w.Branch := by
  cases w <;> dsimp [Work.Branch] <;> infer_instance

def Work.child {K : ℕ} (w : Work K) (b : w.Branch) (right : Bool) : CanonicalHistory K :=
  match w with
  | .stageA h => .afterA ⟨h, b, right⟩
  | .stageB h => .afterB ⟨h, b, right⟩
  | .stageC h => .afterC (h, b, right)

def Work.splitShape {K : ℕ} (w : Work K) (b : w.Branch) : Shape :=
  match w with
  | .stageA h => aSplit ⟨h, b, false⟩
  | .stageB h => bSplit ⟨h, b, false⟩
  | .stageC h => cSplit (h, b, false)

abbrev PlacedWork (K : ℕ) := Work K × Placement
abbrev Active (K tick : ℕ) := {w : PlacedWork K //
  FiniteSchedule.lotTick w.1.lot w.1.stage = tick}

theorem active_tick_lt {K tick : ℕ} (h : Active K tick) : tick < K + 2 := by
  rw [← h.property]
  exact FiniteSchedule.lotTick_lt h.val.1.lot h.val.1.stage

def branchPopulation {K : ℕ} (allocation : Allocation) (dilation : ℕ)
    (w : PlacedWork K) (b : w.1.Branch) : ℕ :=
  population allocation dilation (w.1.child b false, w.2)

theorem branchPopulation_half {K : ℕ} (allocation : Allocation) (dilation : ℕ)
    (w : PlacedWork K) (b : w.1.Branch) (right : Bool) :
    population allocation dilation (w.1.child b right, w.2) =
      branchPopulation allocation dilation w b := by
  rcases w with ⟨w, phi⟩
  cases right with
  | false => rfl
  | true =>
      cases w with
      | stageA h => exact (a_half_counts_eq allocation dilation h b phi).symm
      | stageB h => exact (b_half_counts_eq allocation dilation h b phi).symm
      | stageC h => exact (c_half_counts_eq allocation dilation h b phi).symm

theorem branchPopulation_sum {K : ℕ} (allocation : Allocation) (dilation : ℕ)
    (w : PlacedWork K) :
    (∑ b : w.1.Branch, branchPopulation allocation dilation w b) =
      population allocation dilation (w.1.source, w.2) := by
  rcases w with ⟨w, phi⟩
  cases w with
  | stageA h => exact a_population_transition allocation dilation h false phi
  | stageB h => exact b_population_transition allocation dilation h false phi
  | stageC h => exact c_population_transition allocation dilation h false phi

def terminal {K : ℕ} : CanonicalHistory K → Prop
  | .initial h => initialShape h ∉ positiveInitial
  | .afterA h => aShape h ∉ positiveSecond
  | .afterB h => positive (bShape h) ≠ true
  | .partC _ => False
  | .afterC _ => True

def resident {K : ℕ} (tick : ℕ) : CanonicalHistory K → Prop
  | .initial h => initialShape h ∈ positiveInitial → tick ≤ h.1.val
  | .afterA h => h.1.val.1.val + 1 ≤ tick ∧
      (aShape h ∈ positiveSecond → tick ≤ h.1.val.1.val + 1)
  | .afterB h => h.1.val.1.val.1.val + 2 ≤ tick ∧ positive (bShape h) ≠ true
  | .partC h => tick = h.1.val.1.val.1.val.1.val + 2
  | .afterC h => h.1.1.val.1.val.1.val.1.val + 3 ≤ tick

abbrev State (K tick : ℕ) := {h : History K // resident tick h.1}

theorem terminal_carries {K tick : ℕ} (h : CanonicalHistory K)
    (hr : resident tick h) (ht : terminal h) : resident (tick + 1) h := by
  cases h with
  | initial h => exact fun hp => False.elim (ht hp)
  | afterA h => exact ⟨by have := hr.1; omega, fun hp => False.elim (ht hp)⟩
  | afterB h => exact ⟨by have := hr.1; omega, hr.2⟩
  | partC h => exact False.elim ht
  | afterC h => dsimp [resident] at hr ⊢; omega

theorem work_source_resident {K : ℕ} (w : Work K) :
    resident (FiniteSchedule.lotTick w.lot w.stage) w.source := by
  cases w with
  | stageA h => simp [resident, Work.source, Work.lot, Work.stage,
      initialAncestor, FiniteSchedule.lotTick]
  | stageB h => simp [resident, Work.source, Work.lot, Work.stage,
      initialAncestor, FiniteSchedule.lotTick]
  | stageC h => simp [resident, Work.source, Work.lot, Work.stage,
      initialAncestor, FiniteSchedule.lotTick]

theorem a_child_resident {K : ℕ} (h : InitialPositive K) (b : ASplit h) (right : Bool) :
    resident (h.val.1.val + 1) (.afterA ⟨h, b, right⟩) := by
  simp [resident]

theorem c_child_resident {K : ℕ} (h : PartC K) (b : Fin 4) (right : Bool) :
    resident ((Work.stageC h).lot.val + 3) (.afterC (h, b, right)) := by
  simp [resident, Work.lot, Work.source, initialAncestor]

end MatrixMultiplication.AllFieldHistory

end

end OAI
