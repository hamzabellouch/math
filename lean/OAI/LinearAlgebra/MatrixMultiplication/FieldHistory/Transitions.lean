import OAI.LinearAlgebra.MatrixMultiplication.FieldHistory.Counts

namespace OAI

/-! Finite extraction histories, inherited masks and recovery bounds. -/

noncomputable section
namespace MatrixMultiplication.AllFieldHistory

open AllFieldParameters
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq

def due {K : ℕ} (tick : ℕ) : CanonicalHistory K → Prop
  | .initial h => initialShape h ∈ positiveInitial ∧ tick = h.1.val
  | .afterA h => aShape h ∈ positiveSecond ∧ tick = h.1.val.1.val + 1
  | .afterB _ => False
  | .partC h => tick = h.1.val.1.val.1.val.1.val + 2
  | .afterC _ => False

def produced {K : ℕ} (tick : ℕ) : CanonicalHistory K → Prop
  | .initial _ => False
  | .afterA h => tick = h.1.val.1.val
  | .afterB h => tick = h.1.val.1.val.1.val + 1 ∧ positive (bShape h) ≠ true
  | .partC h => tick = h.1.val.1.val.1.val.1.val + 1
  | .afterC h => tick = h.1.1.val.1.val.1.val.1.val + 2

abbrev Carried (K tick : ℕ) := {h : State K tick // ¬ due tick h.val.1}
abbrev Produced (K tick : ℕ) := {h : History K // produced tick h.1}

theorem produced_not_resident {K tick : ℕ} (h : CanonicalHistory K)
    (hp : produced tick h) : ¬ resident tick h := by
  cases h with
  | initial h => exact False.elim hp
  | afterA h => simp only [produced] at hp; simp only [resident]; omega
  | afterB h => simp only [produced] at hp; simp only [resident]; omega
  | partC h => simp only [produced] at hp; simp only [resident]; omega
  | afterC h => simp only [produced] at hp; simp only [resident]; omega

theorem resident_succ_iff {K tick : ℕ} (h : CanonicalHistory K) :
    resident (tick + 1) h ↔ (resident tick h ∧ ¬ due tick h) ∨ produced tick h := by
  cases h with
  | initial h =>
      by_cases hp : initialShape h ∈ positiveInitial
      · simp only [resident, due, produced, hp, true_implies, true_and, or_false]
        omega
      · simp [resident, due, produced, hp]
  | afterA h =>
      by_cases hp : aShape h ∈ positiveSecond
      · simp only [resident, due, produced, hp, true_implies, true_and]
        omega
      · simp only [resident, due, produced, hp, false_implies, and_true, false_and,
          not_false_eq_true]
        omega
  | afterB h =>
      by_cases hp : positive (bShape h) = true
      · simp [resident, due, produced, hp]
      · simp [resident, due, produced, hp, ne_eq]
        omega
  | partC h => simp only [resident, due, produced]; omega
  | afterC h => simp only [resident, due, produced, not_false_eq_true, and_true]; omega

def stateTransitionForward {K tick : ℕ} (h : State K (tick + 1)) :
    Carried K tick ⊕ Produced K tick := by
  by_cases hr : resident tick h.val.1
  · refine Sum.inl ⟨⟨h.val, hr⟩, ?_⟩
    rcases (resident_succ_iff h.val.1).mp h.property with hc | hp
    · exact hc.2
    · exact False.elim (produced_not_resident _ hp hr)
  · refine Sum.inr ⟨h.val, ?_⟩
    rcases (resident_succ_iff h.val.1).mp h.property with hc | hp
    · exact False.elim (hr hc.1)
    · exact hp

def stateTransitionBackward {K tick : ℕ} : Carried K tick ⊕ Produced K tick →
    State K (tick + 1)
  | .inl h => ⟨h.val.val, (resident_succ_iff _).mpr (.inl ⟨h.val.property, h.property⟩)⟩
  | .inr h => ⟨h.val, (resident_succ_iff _).mpr (.inr h.property)⟩

def stateTransition {K tick : ℕ} : State K (tick + 1) ≃ Carried K tick ⊕ Produced K tick where
  toFun := stateTransitionForward
  invFun := stateTransitionBackward
  left_inv h := by
    unfold stateTransitionForward
    split_ifs <;> rfl
  right_inv h := by
    cases h with
    | inl h => simp [stateTransitionForward, stateTransitionBackward, h.val.property]
    | inr h =>
        have hn := produced_not_resident h.val.1 h.property
        simp [stateTransitionForward, stateTransitionBackward, hn]

def productionParent {K tick : ℕ} (p : Produced K tick) : Active K tick := by
  rcases p with ⟨⟨h, phi⟩, hp⟩
  cases h with
  | initial h => exact False.elim hp
  | afterA h =>
      refine ⟨(.stageA h.1, phi), ?_⟩
      exact hp.symm
  | afterB h =>
      refine ⟨(.stageB h.1, phi), ?_⟩
      exact hp.1.symm
  | partC h =>
      refine ⟨(.stageB h.1.val.1, phi), ?_⟩
      exact hp.symm
  | afterC h =>
      refine ⟨(.stageC h.1, phi), ?_⟩
      exact hp.symm

abbrev DueState (K tick : ℕ) := {h : State K tick // due tick h.val.1}

def activeToDue {K tick : ℕ} (w : Active K tick) : DueState K tick := by
  refine ⟨⟨(w.val.1.source, w.val.2), ?_⟩, ?_⟩
  · exact Eq.mp (congrArg (fun n => resident n w.val.1.source) w.property)
      (work_source_resident w.val.1)
  · rcases w with ⟨⟨w, phi⟩, hw⟩
    cases w with
    | stageA h => exact ⟨h.property, hw.symm⟩
    | stageB h => exact ⟨h.property, hw.symm⟩
    | stageC h => exact hw.symm

def dueToActive {K tick : ℕ} (h : DueState K tick) : Active K tick := by
  rcases h with ⟨⟨⟨h, phi⟩, hr⟩, hd⟩
  cases h with
  | initial h => exact ⟨(.stageA ⟨h, hd.1⟩, phi), hd.2.symm⟩
  | afterA h => exact ⟨(.stageB ⟨h, hd.1⟩, phi), hd.2.symm⟩
  | afterB h => exact False.elim hd
  | partC h => exact ⟨(.stageC h, phi), hd.symm⟩
  | afterC h => exact False.elim hd

def activeSourceEquiv {K tick : ℕ} : Active K tick ≃ DueState K tick where
  toFun := activeToDue
  invFun := dueToActive
  left_inv w := by
    rcases w with ⟨⟨w, phi⟩, hw⟩
    cases w <;> rfl
  right_inv h := by
    rcases h with ⟨⟨⟨h, phi⟩, hr⟩, hd⟩
    cases h with
    | initial h => rfl
    | afterA h => rfl
    | afterB h => exact False.elim hd
    | partC h => rfl
    | afterC h => exact False.elim hd

def bSubdivisionPositionEquiv {K : ℕ} (allocation : Allocation) (dilation : ℕ)
    (h : BPositive K) (phi : Placement) :
    Fin (population allocation dilation (.afterB h.val, phi)) ≃
      (Σ i : Fin 3, Fin (population allocation dilation (.partC (h, i), phi))) :=
  Fintype.equivOfCardEq (by
    simp only [Fintype.card_fin, Fintype.card_sigma]
    exact (part_population_transition allocation dilation h phi).symm)

theorem final_state_terminal {K : ℕ} (h : State K (K + 2)) : terminal h.val.1 := by
  have hr := h.property
  have hlot := (initialAncestor h.val.1).1.isLt
  cases hh : h.val.1 with
  | initial g =>
      simp only [hh, resident] at hr
      simp only [hh, initialAncestor] at hlot
      intro hp
      have := hr hp
      omega
  | afterA a =>
      simp only [hh, resident] at hr
      simp only [hh, initialAncestor] at hlot
      intro hp
      have := hr.2 hp
      omega
  | afterB b =>
      simp only [hh, resident] at hr
      exact hr.2
  | partC c =>
      simp only [hh, resident] at hr
      simp only [hh, initialAncestor] at hlot
      omega
  | afterC c => trivial

end MatrixMultiplication.AllFieldHistory

end

end OAI
