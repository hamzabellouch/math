import OAI.NumberTheory.Ostmann.Construction.SelectedFinalPermutation
import OAI.NumberTheory.Ostmann.Construction.ScheduledFullFinalPermutation

namespace OAI

/-! # Selected-bulk permutations on all actual surviving prime coordinates -/
namespace Ostmann
open scoped Classical BigOperators

noncomputable def selectedFullFinalPerm {I : Type*} (role : I → CopyScheduleRole)
    (n m : ℕ) (bulk : Fin m ↪ I) (hbulk : ∀ i, role (bulk i) = .word)
    (e : FinalParityReassignments n m) : Equiv.Perm (CopyScheduleAtoms role (n + 1)) :=
  ((scheduleHSurvivorEquiv role (n + 1)).permCongr
    (selectedFinalPerm role n m bulk hbulk e)).subtypeCongr (Equiv.refl _)

theorem selectedFullFinalPerm_active {I : Type*} (role : I → CopyScheduleRole)
    (n m : ℕ) (bulk : Fin m ↪ I) (hbulk : ∀ i, role (bulk i) = .word)
    (e : FinalParityReassignments n m) (h : CopyScheduleH role (n + 1)) :
    selectedFullFinalPerm role n m bulk hbulk e ⟨h.val, h.property.1⟩ =
      ⟨(selectedFinalPerm role n m bulk hbulk e h).val,
        (selectedFinalPerm role n m bulk hbulk e h).property.1⟩ := by
  have hh := Equiv.Perm.subtypeCongr.left_apply_subtype
    ((scheduleHSurvivorEquiv role (n + 1)).permCongr
      (selectedFinalPerm role n m bulk hbulk e)) (Equiv.refl _)
    (scheduleHSurvivorEquiv role (n + 1) h)
  exact hh

theorem selectedFullFinalPerm_inactive {I : Type*} (role : I → CopyScheduleRole)
    (n m : ℕ) (bulk : Fin m ↪ I) (hbulk : ∀ i, role (bulk i) = .word)
    (e : FinalParityReassignments n m) (q : CopyScheduleAtoms role (n + 1))
    (hq : (copyScheduleRole role (n + 1) q.val).copiedAt (n + 1) ≠ true) :
    selectedFullFinalPerm role n m bulk hbulk e q = q := by
  unfold selectedFullFinalPerm
  simp only [Equiv.Perm.subtypeCongr.apply, dite_eq_right hq, Equiv.refl_apply]

theorem selectedFullFinalPerm_origin {I : Type*} (role : I → CopyScheduleRole)
    (n m : ℕ) (bulk : Fin m ↪ I) (hbulk : ∀ i, role (bulk i) = .word)
    (e : FinalParityReassignments n m) (q : CopyScheduleAtoms role (n + 1)) :
    copyScheduleOrigin (n + 1) (selectedFullFinalPerm role n m bulk hbulk e q).val =
      copyScheduleOrigin (n + 1) q.val := by
  by_cases hq : (copyScheduleRole role (n + 1) q.val).copiedAt (n + 1) = true
  · have he := selectedFullFinalPerm_active role n m bulk hbulk e ⟨q.val, q.property, hq⟩
    rw [he]
    exact selectedFinalPerm_origin role n m bulk hbulk e _
  · rw [selectedFullFinalPerm_inactive role n m bulk hbulk e q hq]

theorem selectedFullFinalPerm_product_prior {I A : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (n m : ℕ)
    (bulk : Fin m ↪ I) (hbulk : ∀ i, role (bulk i) = .word) (e : FinalParityReassignments n m)
    (μ : I → A → ℝ) (x : CopyScheduleAtoms role (n + 1) → A) :
    (∏ i, μ (copyScheduleOrigin (n + 1) i.val)
      (x (selectedFullFinalPerm role n m bulk hbulk e i))) =
    ∏ i, μ (copyScheduleOrigin (n + 1) i.val) (x i) := by
  calc
    _ = ∏ i, μ (copyScheduleOrigin (n + 1)
        (selectedFullFinalPerm role n m bulk hbulk e i).val)
        (x (selectedFullFinalPerm role n m bulk hbulk e i)) := by
      apply Finset.prod_congr rfl
      intro i _
      rw [selectedFullFinalPerm_origin]
    _ = _ := Equiv.prod_comp (selectedFullFinalPerm role n m bulk hbulk e)
      (fun i => μ (copyScheduleOrigin (n + 1) i.val) (x i))

noncomputable def selectedFullSamplePerm {I A : Type*} (role : I → CopyScheduleRole)
    (n m : ℕ) (bulk : Fin m ↪ I) (hbulk : ∀ i, role (bulk i) = .word)
    (e : FinalParityReassignments n m) :
    (CopyScheduleAtoms role (n + 1) → A) ≃ (CopyScheduleAtoms role (n + 1) → A) :=
  Equiv.arrowCongr (selectedFullFinalPerm role n m bulk hbulk e).symm (Equiv.refl A)

theorem selectedFullSamplePerm_mean {I A : Type*} [Fintype I] [Fintype A]
    (role : I → CopyScheduleRole) (n m : ℕ)
    (bulk : Fin m ↪ I) (hbulk : ∀ i, role (bulk i) = .word) (e : FinalParityReassignments n m)
    (μ : I → A → ℝ) (F : (CopyScheduleAtoms role (n + 1) → A) → ℂ) :
    (∑ x, ((∏ i, μ (copyScheduleOrigin (n + 1) i.val) (x i) : ℝ) : ℂ) *
      F (selectedFullSamplePerm role n m bulk hbulk e x)) =
    ∑ x, ((∏ i, μ (copyScheduleOrigin (n + 1) i.val) (x i) : ℝ) : ℂ) * F x := by
  have h := (selectedFullSamplePerm (A := A) role n m bulk hbulk e).sum_comp
    (fun x => ((∏ i, μ (copyScheduleOrigin (n + 1) i.val) (x i) : ℝ) : ℂ) * F x)
  refine Eq.trans ?_ h
  ·
    apply Finset.sum_congr rfl
    intro x _
    congr 1
    exact congrArg (fun r : ℝ => (r : ℂ))
      (selectedFullFinalPerm_product_prior role n m bulk hbulk e μ x).symm

end Ostmann

end OAI
