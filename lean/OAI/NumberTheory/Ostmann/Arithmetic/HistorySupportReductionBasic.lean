import OAI.NumberTheory.Ostmann.Arithmetic.HistorySupportDescent
import OAI.NumberTheory.Ostmann.Arithmetic.HistorySupportDescentTests
import OAI.NumberTheory.Ostmann.Construction.HistoryGiantGuard

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic.HistorySupportReduction
open Construction
open HistorySupportDescent

def RootData (V : ℕ → ℕ) {l : ℕ} (h : History l) : Prop :=
  h.root.Positive ∧ h.root.PrimeSmall ∧ h.root.TemplateAt l ∧
    h.root.frequency≠0 ∧ h.root.frequency.natAbs≤V l ∧ h.GiantUnits

def LargePrimes (V : ℕ → ℕ) : {l : ℕ} → History l → Prop
  | _, .leaf a => ∀q∈a.small,V 0<q.value
  | l+1, .node a _ u _ _ left right =>
      (∀q∈a.small,V (l+1)<q.value) ∧ (∀q∈u,V (l+1)<q.value) ∧
        LargePrimes V left ∧ LargePrimes V right

def LocalTests (outside : List ℕ) (a : State) (p : ℕ) (u hp hm : List SmallSlot)
    (v w : ℤ) : Prop :=
  (u.map SmallSlot.value).Nodup ∧ (∀b∈u,Nat.Prime b.value) ∧
    (∀b∈u,¬(b.value:ℤ)*b.value ∣ reversalNumerator v w
      ((a.giantPlus*(hp.map SmallSlot.value).prod:ℕ):ℤ)
      ((a.giantMinus*(hm.map SmallSlot.value).prod:ℕ):ℤ)) ∧
    (∀q∈outside,Nat.Coprime p q) ∧ (∀b∈u,∀q∈outside,Nat.Coprime b.value q)

def Reduced (V : ℕ → ℕ) (outside : List ℕ) : {l : ℕ} → History l → Prop
  | _, h => RootData V h ∧ match h with
    | .leaf _ => True
    | @History.node l a p u hp hm left right =>
        History.nodeRelations (l+1) a p u hp hm left.root right.root ∧
        LocalTests outside a p u hp hm left.root.frequency right.root.frequency ∧
        Reduced V outside left ∧ Reduced V outside right
termination_by l _ => l

theorem root_frequency_mem {l : ℕ} (h : History l) : h.root.frequency∈h.frequencies := by
  cases h <;> simp [History.root,History.frequencies]

theorem rootData_of_supported {V : ℕ → ℕ} {outside : List ℕ} {l : ℕ}
    {h : History l} (hs : h.Supported V outside) : RootData V h := by
  rw [History.Supported.eq_def] at hs
  exact ⟨hs.1,hs.2.1,hs.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,hs.2.2.2.2.2.2.1⟩

theorem largePrimes_root {V : ℕ → ℕ} {l : ℕ} {h : History l}
    (hs : LargePrimes V h) : ∀q∈h.root.small,V l<q.value := by
  cases h with
  | leaf a => exact hs
  | node a p u hp hm left right => exact hs.1

theorem root_frequency_small_units {V : ℕ → ℕ} {l : ℕ} {h : History l}
    (hs : RootData V h) (hlarge : ∀q∈h.root.small,V l<q.value) :
    ∀q∈h.root.small,IsCoprime h.root.frequency (q.value:ℤ) := by
  intro q hq
  have hc := History.prime_coprime_small_frequency (hs.2.1 q hq) hs.2.2.2.1
    (hs.2.2.2.2.1.trans_lt (hlarge q hq))
  apply Int.isCoprime_iff_nat_coprime.mpr
  simpa only [Int.natAbs_natCast] using hc.symm

theorem inherited_frequency_unit {V : ℕ → ℕ} {l : ℕ} {h : History l}
    (hs : RootData V h) (hlarge : ∀q∈h.root.small,V l<q.value)
    {X : ℕ} {u inherited : List SmallSlot}
    (hminus : h.root.giantMinus=X) (hsmall : h.root.small.Perm (u++inherited)) :
    IsCoprime h.root.frequency ((X*(inherited.map SmallSlot.value).prod:ℕ):ℤ) := by
  rw [Nat.cast_mul,IsCoprime.mul_right_iff]
  constructor
  · have hg := (hs.2.2.2.2.2 _ (root_frequency_mem h)).2
    rw [hminus] at hg
    apply Int.isCoprime_iff_nat_coprime.mpr
    simpa only [Int.natAbs_natCast] using hg.symm
  · apply frequency_prod_coprime
    intro q hq
    obtain ⟨b,hb,rfl⟩ := List.mem_map.mp hq
    exact root_frequency_small_units hs hlarge b
      (hsmall.mem_iff.mpr (List.mem_append_right u hb))

theorem child_list_coprime_of_state {child : State} {p X : ℕ}
    {u inherited : List SmallSlot} {outside : List ℕ}
    (hplus : child.giantPlus=p) (hminus : child.giantMinus=X)
    (hsmall : child.small.Perm (u++inherited)) (hc : child.Coprime outside) :
    ((p::X::(u++inherited).map SmallSlot.value)++outside).Pairwise Nat.Coprime := by
  have hp : child.values.Perm (p::X::(u++inherited).map SmallSlot.value) := by
    simpa only [State.values,hplus,hminus] using
      List.Perm.cons p (List.Perm.cons X (hsmall.map SmallSlot.value))
  exact ((hp.append_right outside).pairwise_iff Nat.Coprime.symm).mp hc

end Ostmann.Arithmetic.HistorySupportReduction

end

end OAI
