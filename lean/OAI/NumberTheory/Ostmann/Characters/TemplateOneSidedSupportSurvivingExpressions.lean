import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedRelabelTemplate
import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedSupportSurviving

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Characters.TemplateOneSidedSupportSurviving
open Template SymbolicHistory TemplateOneSidedBudget TemplateOneSidedRelabel
open scoped BigOperators
attribute [local instance] Classical.propDecidable

def groupedExpressions (k j : ℕ) (width : Role→ℕ) (P : ℤ)
    (e : Equiv.Perm (CopiedConstituent (schedule k j) j width)) :
    Expressions (ι:=(Σi:SurvivingSlot k j,Fin (survivingWidth k j width i))) k j :=
  relabelExpressions (survivingPrimeEquiv k j width).symm
    (survivingSampledExpressions k j width P e)

def groupedPermutation (k j : ℕ) (width : Role→ℕ)
    (e : Equiv.Perm (CopiedConstituent (schedule k j) j width)) :
    Equiv.Perm (Σi:SurvivingSlot k j,Fin (survivingWidth k j width i)) :=
  ((survivingPrimeEquiv k j width).trans (Equiv.sumCongr e (Equiv.refl _))).trans
    (survivingPrimeEquiv k j width).symm

theorem groupedExpressions_eval (k j : ℕ) (width : Role→ℕ) (P : ℤ)
    (e : Equiv.Perm (CopiedConstituent (schedule k j) j width))
    (x : (Σi:SurvivingSlot k j,Fin (survivingWidth k j width i))→ℤ) :
    evalExpressions x (groupedExpressions k j width P e) =
      sourceState k j P
        (fun i=>∏a,x ((survivingPrimeEquiv k j width).symm (.inl (e ⟨i,a⟩))))
        (fun i=>∏a,x ⟨.inr i,a⟩) := by
  rw [groupedExpressions,relabelExpressions_eval,survivingSampledExpressions_eval]
  rfl

theorem groupedExpressions_reference_eval (k j : ℕ) (width : Role→ℕ) (P : ℤ)
    (x : (Σi:SurvivingSlot k j,Fin (survivingWidth k j width i))→ℤ) :
    evalExpressions x (groupedExpressions k j width P (Equiv.refl _)) =
      sourceState k j P (fun i=>∏a,x ⟨.inl i,a⟩) (fun i=>∏a,x ⟨.inr i,a⟩) :=
  groupedExpressions_eval k j width P (Equiv.refl _) x

theorem groupedExpressions_matches (k j : ℕ) (width : Role→ℕ) (P : ℤ)
    (x : (Σi:SurvivingSlot k j,Fin (survivingWidth k j width i))→ℤ) :
    (origins k j).Matches (fun i=>∏a,x ⟨i,a⟩)
      (evalExpressions x (groupedExpressions k j width P (Equiv.refl _))) := by
  rw [groupedExpressions_reference_eval]
  exact origins_matches_products k j width P x

theorem groupedExpressions_good (k j : ℕ) (width : Role→ℕ) (P : ℤ)
    (e : Equiv.Perm (CopiedConstituent (schedule k j) j width))
    (x : (Σi:SurvivingSlot k j,Fin (survivingWidth k j width i))→ℤ)
    (i : (schedule k j).Slot) :
    HistoryReconstruction.Good x (groupedExpressions k j width P e i) :=
  (relabel_good _ _ _).mpr (survivingSampledExpressions_good k j width P e _ i)

theorem survivingSampledExpressions_relabel (k j : ℕ) (width : Role→ℕ) (P : ℤ)
    (e : Equiv.Perm (CopiedConstituent (schedule k j) j width)) :
    relabelExpressions (Equiv.sumCongr e (Equiv.refl _))
      (survivingSampledExpressions k j width P (Equiv.refl _)) =
        survivingSampledExpressions k j width P e := by
  unfold survivingSampledExpressions
  rw [← childExpressions_relabel]
  congr 1
  funext i
  cases i with
  | inl z =>
    simp only [relabelExpressions,survivingPairedExpressions]
    rw [relabel_finiteProductExpression]
    rfl
  | inr i =>
    simp only [relabelExpressions,survivingPairedExpressions]
    rw [relabel_finiteProductExpression]
    rfl

theorem groupedExpressions_relabel (k j : ℕ) (width : Role→ℕ) (P : ℤ)
    (e : Equiv.Perm (CopiedConstituent (schedule k j) j width)) :
    relabelExpressions (groupedPermutation k j width e)
      (groupedExpressions k j width P (Equiv.refl _)) =
        groupedExpressions k j width P e := by
  unfold groupedExpressions
  rw [← survivingSampledExpressions_relabel k j width P e]
  funext i
  simp only [relabelExpressions,relabel_comp]
  congr 1
  funext v
  simp only [groupedPermutation,Equiv.trans_apply,Equiv.apply_symm_apply]

theorem groupedExpressions_prime_eval (k j : ℕ) (width : Role→ℕ) (P : ℤ)
    (e : Equiv.Perm (CopiedConstituent (schedule k j) j width)) {Q : ℕ}
    (p : SurvivingPrimeIndex k j width→Preliminaries.PrimeUpTo Q) :
    evalExpressions (fun i=>((p (survivingPrimeEquiv k j width i)).val:ℤ))
      (groupedExpressions k j width P e) =
    sourceState k j P (copiedSampleState (schedule k j) j width (fun i=>p (.inl (e i))))
      (outsideSampleState (schedule k j) j width (fun i=>p (.inr i))) := by
  rw [groupedExpressions,relabelExpressions_eval]
  simp only [Equiv.apply_symm_apply]
  have h := survivingSampledExpressions_prime_eval k j width P e
    (fun i=>p (.inl i)) (fun i=>p (.inr i))
  have hp : (fun i=>((Sum.elim (fun v=>p (.inl v)) (fun v=>p (.inr v)) i).val:ℤ)) =
      (fun i=>((p i).val:ℤ)) := by
    funext i
    cases i <;> rfl
  rw [hp] at h
  exact h

end Ostmann.Characters.TemplateOneSidedSupportSurviving

end

end OAI
