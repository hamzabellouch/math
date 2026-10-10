import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkReferenceFrequencyFamilyRoots

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkPrincipalSourceReindex
open Construction HistoryBulkReferenceFrequencyFamily
open scoped BigOperators
attribute [local instance] Classical.propDecidable

def extendCommonRoot {α : Type*} [Zero α] (V : ℕ → ℕ) (l : ℕ)
    (F : RootFrequencyIndex V l → α) (i : FrequencyChoices V (l+1)) : α :=
  if i.1=i.2.1 then F (i.1,i.2.2) else 0

theorem extendCommonRoot_diagonal {α : Type*} [Zero α] (V : ℕ → ℕ) (l : ℕ)
    (F : RootFrequencyIndex V l → α) (i : RootFrequencyIndex V l) :
    extendCommonRoot V l F (i.1,i.1,i.2)=F i := by
  simp only [extendCommonRoot,ite_true]

theorem sum_extendCommonRoot {α : Type*} [AddCommMonoid α] (V : ℕ → ℕ) (l : ℕ)
    (F : RootFrequencyIndex V l → α) :
    (∑i : FrequencyChoices V (l+1),extendCommonRoot V l F i)=∑i,F i := by
  classical
  change (∑i : AllowedFrequency V l × AllowedFrequency V l × FrequencyChoices V l × FrequencyChoices V l,
    if i.1=i.2.1 then F (i.1,i.2.2) else 0)=_
  rw [Fintype.sum_prod_type,Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro v _
  rw [Fintype.sum_prod_type,Finset.sum_comm]
  simp only [Finset.sum_ite_eq,Finset.mem_univ,ite_true]

def extendCommonRootOption {α : Type*} (V : ℕ → ℕ) (l : ℕ)
    (F : RootFrequencyIndex V l → Option α) (i : FrequencyChoices V (l+1)) : Option α :=
  if i.1=i.2.1 then F (i.1,i.2.2) else none

theorem sum_extendCommonRootOption {α β : Type*} [AddCommMonoid β]
    (V : ℕ → ℕ) (l : ℕ) (F : RootFrequencyIndex V l → Option α) (G : α → β) :
    (∑i : FrequencyChoices V (l+1),(extendCommonRootOption V l F i).elim 0 G)=
      ∑i : RootFrequencyIndex V l,(F i).elim 0 G := by
  rw [←sum_extendCommonRoot V l (fun i=>(F i).elim 0 G)]
  apply Finset.sum_congr rfl
  intro i _
  unfold extendCommonRootOption extendCommonRoot
  split <;> rfl

end Ostmann.Arithmetic.HistoryBulkPrincipalSourceReindex

end

end OAI
