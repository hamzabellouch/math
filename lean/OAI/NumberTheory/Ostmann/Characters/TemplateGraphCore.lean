import OAI.NumberTheory.Ostmann.Characters.AnchorCodes
import OAI.NumberTheory.Ostmann.Characters.TemplateSchedule
import OAI.NumberTheory.Ostmann.Characters.TransferAlgebra

namespace OAI

noncomputable section
namespace Ostmann.Characters.Template
attribute [local instance] Classical.propDecidable
local instance (T : Layout) : DecidableEq T.Slot := Classical.decEq _

def oldIndex (T : Layout) (j : ℕ) (p : {i:T.Slot // T.IsPivot j i}) :
    Option ({i:T.Slot // T.IsCopied j i} ⊕ {i:T.Slot // T.IsOutside j i}) → T.Slot
  | none => p.val
  | some (.inl i) => i.val
  | some (.inr i) => i.val

theorem oldIndex_injective (T : Layout) (j : ℕ) (p : {i:T.Slot // T.IsPivot j i}) :
    Function.Injective (oldIndex T j p) := by
  intro x y h
  cases x with
  | none =>
    cases y with
    | none => rfl
    | some y =>
      cases y with
      | inl i =>
        simp only [oldIndex] at h
        exact False.elim (pivot_not_copied T j p.val p.property (h.symm ▸ i.property))
      | inr i =>
        simp only [oldIndex] at h
        exact False.elim (i.property.1 (h ▸ p.property))
  | some x =>
    cases y with
    | none =>
      cases x with
      | inl i =>
        simp only [oldIndex] at h
        exact False.elim (pivot_not_copied T j p.val p.property (h ▸ i.property))
      | inr i =>
        simp only [oldIndex] at h
        exact False.elim (i.property.1 (h.symm ▸ p.property))
    | some y =>
      cases x with
      | inl i =>
        cases y with
        | inl r => exact congrArg (fun z => some (Sum.inl z)) (Subtype.ext h)
        | inr r =>
          simp only [oldIndex] at h
          exact False.elim (r.property.2 (h ▸ i.property))
      | inr i =>
        cases y with
        | inl r =>
          simp only [oldIndex] at h
          exact False.elim (i.property.2 (h.symm ▸ r.property))
        | inr r => exact congrArg (fun z => some (Sum.inr z)) (Subtype.ext h)

def oldIndexEquiv (T : Layout) (j : ℕ) (p : {i:T.Slot // T.IsPivot j i})
    (hp : ∀q:{i:T.Slot // T.IsPivot j i},q=p) :
    Option ({i:T.Slot // T.IsCopied j i} ⊕ {i:T.Slot // T.IsOutside j i}) ≃ T.Slot :=
  Equiv.ofBijective (oldIndex T j p) ⟨oldIndex_injective T j p,by
    intro i
    by_cases hi : T.IsPivot j i
    · exact ⟨none,congrArg Subtype.val (hp ⟨i,hi⟩).symm⟩
    · by_cases hc : T.IsCopied j i
      · exact ⟨some (.inl ⟨i,hc⟩),rfl⟩
      · exact ⟨some (.inr ⟨i,hi,hc⟩),rfl⟩⟩

def graphStep (T : Layout) (j : ℕ) (p : {i:T.Slot // T.IsPivot j i})
    (b : T.Slot → T.Slot → ℤ) : (T.step j).Slot → (T.step j).Slot → ℤ :=
  transferGraph (fun x y => b (oldIndex T j p x) (oldIndex T j p y))

theorem graphStep_regular (T : Layout) (j : ℕ) (p : {i:T.Slot // T.IsPivot j i})
    (b : T.Slot → T.Slot → ℤ) (i : {i:T.Slot // T.IsCopied j i}) (ε : ℤ)
    (hb : ∀z,z≠i.val → b i.val z=ε) (t : Bool) (z : (T.step j).Slot)
    (hz : z≠.inl (i,t)) : graphStep T j p b (.inl (i,t)) z=copySign t*ε := by
  apply transferGraph_regular _ i ε ?_ t z hz
  intro q hq
  apply hb
  intro he
  exact hq (oldIndex_injective T j p he)

@[simp] theorem graphStep_self (T : Layout) (j : ℕ) (p : {i:T.Slot // T.IsPivot j i})
    (b : T.Slot → T.Slot → ℤ) (i : (T.step j).Slot) : graphStep T j p b i i=0 := by
  cases i <;> simp [graphStep,transferGraph]

def copyUnit (t : Bool) : ℤˣ := if t then 1 else -1
@[simp] theorem copyUnit_coe (t : Bool) : (copyUnit t:ℤ)=copySign t := by cases t <;> rfl

def graph (k : ℕ) : (j : ℕ) → (schedule k j).Slot → (schedule k j).Slot → ℤ
  | 0 => fun i h => if i=h then 0 else 1
  | j+1 => if hj:j<k then graphStep (schedule k j) j (pivotSlot k j hj) (graph k j)
      else fun _ _ => 0

def rowSign (k : ℕ) : (j : ℕ) → (schedule k j).Slot → ℤˣ
  | 0 => fun _ => 1
  | j+1 => fun z => match z with
    | .inl (i,t) => copyUnit t * rowSign k j i.val
    | .inr i => rowSign k j i.val

theorem graph_succ (k j : ℕ) (hj : j<k) :
    graph k (j+1)=graphStep (schedule k j) j (pivotSlot k j hj) (graph k j) := by
  simp only [graph,dite_eq_left hj]

@[simp] theorem graph_self (k j : ℕ) (i : (schedule k j).Slot) : graph k j i i=0 := by
  cases j with
  | zero => simp [graph]
  | succ j => by_cases hj:j<k <;> simp [graph,hj]

end Ostmann.Characters.Template

end

end OAI
