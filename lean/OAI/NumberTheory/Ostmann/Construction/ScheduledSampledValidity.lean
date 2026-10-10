import OAI.NumberTheory.Ostmann.Construction.ScheduledNodeEquations
import OAI.NumberTheory.Ostmann.Construction.ScheduledNodeUnits
import OAI.NumberTheory.Ostmann.Construction.SampledPrimeProducts

namespace OAI

/-! # Actual full weights give valid original-prime sampled histories -/

namespace Ostmann
open scoped BigOperators Classical

theorem scheduled_scaled_history_coefficient_units {I : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (childBound pivotBound : ℕ → ℕ)
    (i : I) (hi : role i = .word) (S : Finset ℤ) (n : ℕ)
    (C : CopyScheduleAtoms role n → ℕ) (x : TreeLeafIndex n → ℕ)
    (t : FrequencyTree S n)
    (hu : ∀ k < n, ∀ a b, role a = .pivot k → role b = .pivot k → a = b)
    (hunits : scheduleAtomUnitsValid role childBound pivotBound (totalAtomUnitRanges role) n
      (wordLeafScale role i hi n C x) (frequencyTreeMap Subtype.val n t)) :
    let p := transferPivotArray (scheduleAtomSystem role childBound pivotBound) n
      ⟨n, wordLeafScale role i hi n C x⟩ (frequencyTreeMap Subtype.val n t)
    ∀ j, IsCoprime
        ((scheduledActualSourceScheme role S n t (fun v => (C v : ℤ))).leftCoefficient
          (fun j => (p j : ℤ)) j) (singleTreeNodeFrequencies S n t j.val).root ∧
      IsCoprime
        ((scheduledActualSourceScheme role S n t (fun v => (C v : ℤ))).rightCoefficient
          (fun j => (p j : ℤ)) j) (singleTreeNodeFrequencies S n t j.val).root := by
  intro p j
  have hall := scheduledNodeValues_units role childBound pivotBound S n
    (wordLeafScale role i hi n C x) t hunits j
  have hc (b : Bool) :
      (∏ a : CopyScheduleH role (scheduledNodeLevel n j),
        scheduledNodeValues role n j C p ⟨.inl (b, a.val), a.property⟩).Coprime
          (singleTreeNodeFrequencies S n t j.val).root.natAbs := by
    have hprod := Nat.coprime_fintype_prod_left_iff.mpr
      (fun a : CopyScheduleH role (scheduledNodeLevel n j) => hall ⟨.inl (b, a.val), a.property⟩)
    rw [scheduledNodeValues_H_product] at hprod
    exact (Nat.coprime_mul_iff_left.mp hprod).1
  constructor
  · rw [scheduledActualSourceScheme_left_natCast role S n t C hu]
    apply Int.isCoprime_iff_gcd_eq_one.mpr
    exact hc false
  · rw [scheduledActualSourceScheme_right_natCast role S n t C hu]
    apply Int.isCoprime_iff_gcd_eq_one.mpr
    exact hc true

/-- No equation or unit condition is added to the analytic assumptions: both
are obtained from the actual nonzero full coefficient and its original guards. -/
theorem fullAtomTransferWeight_sampled_valid {I : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (childBound pivotBound : ℕ → ℕ)
    (ranges : (j : ℕ) → List (ScheduleAtomRange role j))
    (leaf : ScheduleAtomState role → ℤ → ℂ)
    (i : I) (hi : role i = .word) (S : Finset ℤ) (n : ℕ)
    (C : CopyScheduleAtoms role n → ℕ) (P : Finset ℕ) (Q : ℕ)
    (hunit : ∀ p : P, (p : ℕ).Coprime Q) (x : TreeLeafIndex n → P)
    (t : FrequencyTree S n)
    (hu : ∀ k < n, ∀ a b, role a = .pivot k → role b = .pivot k → a = b)
    (hw : fullAtomTransferWeight role childBound pivotBound ranges leaf n
      (wordLeafScale role i hi n C (fun j => (x j : ℕ))) (frequencyTreeMap Subtype.val n t) ≠ 0) :
    let p := transferPivotArray (scheduleAtomSystem role childBound pivotBound) n
      ⟨n, wordLeafScale role i hi n C (fun j => (x j : ℕ))⟩ (frequencyTreeMap Subtype.val n t)
    (sampledPrimeHistory P Q n hunit x (fun j => (p j : ℤ))).valid
      (scheduledActualSourceScheme role S n t (fun v => (C v : ℤ))) := by
  intro p
  obtain ⟨hv, hunits⟩ := fullAtomTransferWeight_valid_units role childBound pivotBound ranges leaf n
    (wordLeafScale role i hi n C (fun j => (x j : ℕ))) _ hw
  constructor
  · intro j
    have heq := scheduled_scaled_history_equations role childBound pivotBound i hi S n C
      (fun j => (x j : ℕ)) t hu hv j
    have hp := sampledPrimeHistory_childProducts P Q n hunit x (fun j => (p j : ℤ)) j
    have hL := congrArg Prod.fst hp
    have hR := congrArg Prod.snd hp
    dsimp only at hL hR
    change _ * _ * _ - _ * _ * _ = _ * _
    rw [hL, hR]
    exact heq
  · exact scheduled_scaled_history_coefficient_units role childBound pivotBound i hi S n C
      (fun j => (x j : ℕ)) t hu hunits

end Ostmann

end OAI
