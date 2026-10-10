import OAI.NumberTheory.Ostmann.Construction.ScheduledFinalPermutation
import OAI.NumberTheory.Ostmann.Construction.ConstituentAmplitudeEnergy
import OAI.NumberTheory.Ostmann.Construction.FinalPermutationComparison

namespace OAI

/-! # The final reassignments on every actual surviving prime coordinate -/

namespace Ostmann
open scoped BigOperators Classical

def scheduleHSurvivorEquiv {I : Type*} (role : I → CopyScheduleRole) (n : ℕ) :
    CopyScheduleH role n ≃
      {q : CopyScheduleAtoms role n // (copyScheduleRole role n q.val).copiedAt n = true} where
  toFun q := ⟨⟨q.val, q.property.1⟩, q.property.2⟩
  invFun q := ⟨q.val.val, q.val.property, q.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

noncomputable def scheduledFullFinalPerm {I : Type*} (role : I → CopyScheduleRole)
    (n m : ℕ) (word : Fin m ≃ {i : I // role i = .word})
    (e : FinalParityReassignments n m) : Equiv.Perm (CopyScheduleAtoms role (n + 1)) :=
  ((scheduleHSurvivorEquiv role (n + 1)).permCongr
    (scheduledFinalPerm role n m word e)).subtypeCongr (Equiv.refl _)

theorem scheduledFullFinalPerm_active {I : Type*} (role : I → CopyScheduleRole)
    (n m : ℕ) (word : Fin m ≃ {i : I // role i = .word})
    (e : FinalParityReassignments n m) (h : CopyScheduleH role (n + 1)) :
    scheduledFullFinalPerm role n m word e ⟨h.val, h.property.1⟩ =
      ⟨(scheduledFinalPerm role n m word e h).val,
        (scheduledFinalPerm role n m word e h).property.1⟩ := by
  have hh := Equiv.Perm.subtypeCongr.left_apply_subtype
    ((scheduleHSurvivorEquiv role (n + 1)).permCongr
      (scheduledFinalPerm role n m word e)) (Equiv.refl _)
    (scheduleHSurvivorEquiv role (n + 1) h)
  exact hh

theorem scheduledFullFinalPerm_inactive {I : Type*} (role : I → CopyScheduleRole)
    (n m : ℕ) (word : Fin m ≃ {i : I // role i = .word})
    (e : FinalParityReassignments n m) (q : CopyScheduleAtoms role (n + 1))
    (hq : (copyScheduleRole role (n + 1) q.val).copiedAt (n + 1) ≠ true) :
    scheduledFullFinalPerm role n m word e q = q := by
  unfold scheduledFullFinalPerm
  simp only [Equiv.Perm.subtypeCongr.apply, dite_eq_right hq, Equiv.refl_apply]

theorem scheduledFullFinalPerm_origin {I : Type*} (role : I → CopyScheduleRole)
    (n m : ℕ) (word : Fin m ≃ {i : I // role i = .word})
    (e : FinalParityReassignments n m) (q : CopyScheduleAtoms role (n + 1)) :
    copyScheduleOrigin (n + 1) (scheduledFullFinalPerm role n m word e q).val =
      copyScheduleOrigin (n + 1) q.val := by
  by_cases hq : (copyScheduleRole role (n + 1) q.val).copiedAt (n + 1) = true
  · have he := scheduledFullFinalPerm_active role n m word e ⟨q.val, q.property, hq⟩
    rw [he]
    exact scheduledFinalPerm_origin role n m word e _
  · rw [scheduledFullFinalPerm_inactive role n m word e q hq]

theorem scheduledFullFinalPerm_product_prior {I A : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (n m : ℕ)
    (word : Fin m ≃ {i : I // role i = .word}) (e : FinalParityReassignments n m)
    (μ : I → A → ℝ) (x : CopyScheduleAtoms role (n + 1) → A) :
    (∏ i, μ (copyScheduleOrigin (n + 1) i.val)
      (x (scheduledFullFinalPerm role n m word e i))) =
    ∏ i, μ (copyScheduleOrigin (n + 1) i.val) (x i) := by
  calc
    _ = ∏ i, μ (copyScheduleOrigin (n + 1)
        (scheduledFullFinalPerm role n m word e i).val)
        (x (scheduledFullFinalPerm role n m word e i)) := by
      apply Finset.prod_congr rfl
      intro i _
      rw [scheduledFullFinalPerm_origin]
    _ = _ := Equiv.prod_comp (scheduledFullFinalPerm role n m word e)
      (fun i => μ (copyScheduleOrigin (n + 1) i.val) (x i))

noncomputable def scheduledFullSamplePerm {I A : Type*} (role : I → CopyScheduleRole)
    (n m : ℕ) (word : Fin m ≃ {i : I // role i = .word})
    (e : FinalParityReassignments n m) :
    (CopyScheduleAtoms role (n + 1) → A) ≃ (CopyScheduleAtoms role (n + 1) → A) :=
  Equiv.arrowCongr (scheduledFullFinalPerm role n m word e).symm (Equiv.refl A)

theorem scheduledFullSamplePerm_mean {I A : Type*} [Fintype I] [Fintype A]
    (role : I → CopyScheduleRole) (n m : ℕ)
    (word : Fin m ≃ {i : I // role i = .word}) (e : FinalParityReassignments n m)
    (μ : I → A → ℝ) (F : (CopyScheduleAtoms role (n + 1) → A) → ℂ) :
    (∑ x, ((∏ i, μ (copyScheduleOrigin (n + 1) i.val) (x i) : ℝ) : ℂ) *
      F (scheduledFullSamplePerm role n m word e x)) =
    ∑ x, ((∏ i, μ (copyScheduleOrigin (n + 1) i.val) (x i) : ℝ) : ℂ) * F x := by
  have h := (scheduledFullSamplePerm (A := A) role n m word e).sum_comp
    (fun x => ((∏ i, μ (copyScheduleOrigin (n + 1) i.val) (x i) : ℝ) : ℂ) * F x)
  refine Eq.trans ?_ h
  ·
    apply Finset.sum_congr rfl
    intro x _
    congr 1
    exact congrArg (fun r : ℝ => (r : ℂ))
      (scheduledFullFinalPerm_product_prior role n m word e μ x).symm

end Ostmann

end OAI
