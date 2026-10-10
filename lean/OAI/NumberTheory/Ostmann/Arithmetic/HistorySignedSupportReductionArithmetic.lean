import OAI.NumberTheory.Ostmann.Arithmetic.HistorySignedDecodeRebuild
import OAI.NumberTheory.Ostmann.Arithmetic.HistorySignedSupportReduction

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic.HistorySignedSupportReduction
open Construction HistorySignedDecode

def RootArithmetic (V : ℕ→ℕ) {l : ℕ} (h : SignedHistory l) : Prop :=
  (∀q∈h.root.small,q.value.Prime) ∧
    (∀q∈h.root.small,∀j,q.role=.compensation j→l<j) ∧
    h.root.frequency≠0 ∧ h.root.frequency.natAbs≤V l ∧
    ∀v∈frequencies h,Nat.Coprime h.root.giantPlus.natAbs v.natAbs ∧
      Nat.Coprime h.root.giantMinus.natAbs v.natAbs

def LocalArithmetic (outside : List ℕ) (a : SignedState) (p : ℤ)
    (u hp hm : List SmallSlot) (v w : ℤ) : Prop :=
  (u.map SmallSlot.value).Nodup ∧ (∀b∈u,Nat.Prime b.value) ∧
    (∀b∈u,¬(b.value:ℤ)*b.value ∣ reversalNumerator v w
      (a.giantPlus*((hp.map SmallSlot.value).prod:ℤ))
      (a.giantMinus*((hm.map SmallSlot.value).prod:ℤ))) ∧
    (∀q∈outside,Nat.Coprime p.natAbs q) ∧ (∀b∈u,∀q∈outside,Nat.Coprime b.value q)

def ArithmeticGuards (V : ℕ→ℕ) (outside : List ℕ) : {l : ℕ}→SignedHistory l→Prop
  | _,h => RootArithmetic V h ∧ match h with
    | .leaf _ => True
    | .node a p u hp hm left right =>
      LocalArithmetic outside a p u hp hm left.root.frequency right.root.frequency ∧
      ArithmeticGuards V outside left ∧ ArithmeticGuards V outside right
termination_by l _=>l

def RootCoprime (outside : List ℕ) (a : SignedState) : Prop :=
  ((a.giantPlus.natAbs::a.giantMinus.natAbs::a.small.map SmallSlot.value)++outside).Pairwise Nat.Coprime

def ArithmeticGuarded (V : ℕ→ℕ) (outside : List ℕ) {l : ℕ} (h : SignedHistory l) : Prop :=
  RootCoprime outside h.root ∧ h.IntegralGuard ∧ ArithmeticGuards V outside h

def ResidueRootCoprime (outside : List ℕ) (a : SignedState) : Prop :=
  (a.small.map SmallSlot.value++outside).Pairwise Nat.Coprime ∧
    ∀q∈a.small.map SmallSlot.value++outside,
      Nat.Coprime a.giantPlus.natAbs q ∧ Nat.Coprime a.giantMinus.natAbs q

def ResidueGuarded (V : ℕ→ℕ) (outside : List ℕ) {l : ℕ} (h : SignedHistory l) : Prop :=
  ResidueRootCoprime outside h.root ∧ h.IntegralGuard ∧ ArithmeticGuards V outside h

theorem rootCoprime_iff_giant_and_residue (outside : List ℕ) (a : SignedState) :
    RootCoprime outside a↔Nat.Coprime a.giantPlus.natAbs a.giantMinus.natAbs ∧
      ResidueRootCoprime outside a := by
  simp only [RootCoprime,List.cons_append,List.pairwise_cons,ResidueRootCoprime]
  constructor
  · rintro ⟨hplus,hminus,hsmall⟩
    exact ⟨hplus _ (List.mem_cons_self),hsmall,fun q hq=>
      ⟨hplus q (List.mem_cons_of_mem _ hq),hminus q hq⟩⟩
  · rintro ⟨hgiant,hsmall,hrest⟩
    refine ⟨?_,fun q hq=>(hrest q hq).2,hsmall⟩
    intro q hq
    rcases List.mem_cons.mp hq with rfl | hq
    · exact hgiant
    · exact (hrest q hq).1

theorem arithmeticGuarded_iff_giant_and_residue (V : ℕ→ℕ) (outside : List ℕ)
    {l : ℕ} (h : SignedHistory l) :
    ArithmeticGuarded V outside h↔
      Nat.Coprime h.root.giantPlus.natAbs h.root.giantMinus.natAbs ∧ ResidueGuarded V outside h := by
  simp only [ArithmeticGuarded,ResidueGuarded,rootCoprime_iff_giant_and_residue]
  tauto

def Shape : {l : ℕ}→SignedHistory l→Prop
  | _,.leaf _ => True
  | l+1,.node a p u hp hm left right =>
    (∀q∈u,q.role=.compensation (l+1)) ∧ a.small.Perm (hp++hm) ∧
    left.root.giantPlus=p ∧ right.root.giantPlus=p ∧
    left.root.giantMinus=a.giantPlus ∧ right.root.giantMinus=a.giantMinus ∧
    left.root.small.Perm (u++hp) ∧ right.root.small.Perm (u++hm) ∧ Shape left ∧ Shape right

lemma natAbs_eq_toNat {z : ℤ} (hz : 0≤z) : z.natAbs=z.toNat := by omega

lemma positiveState_of_primes (a : SignedState) (hp : 0<a.giantPlus) (hm : 0<a.giantMinus)
    (hs : ∀q∈a.small,q.value.Prime) : a.toState.Positive := by
  intro v hv
  simp only [State.values,SignedState.toState,List.mem_cons,List.mem_map] at hv
  rcases hv with rfl | rfl | ⟨q,hq,rfl⟩
  · omega
  · omega
  · exact (hs q hq).pos

lemma rootData_iff_arithmetic (V : ℕ→ℕ) {l : ℕ} (h : SignedHistory l)
    (hp : 0<h.root.giantPlus) (hm : 0<h.root.giantMinus) :
    RootData V h↔RootArithmetic V h := by
  simp only [RootData,RootArithmetic,natAbs_eq_toNat hp.le,natAbs_eq_toNat hm.le]
  constructor
  · exact fun h=>h.2
  · intro hh
    exact ⟨positiveState_of_primes _ hp hm hh.1,hh⟩

lemma localTests_iff_arithmetic (outside : List ℕ) (a : SignedState) (p : ℤ)
    (u hp hm : List SmallSlot) (v w : ℤ) (hp0 : 0≤p) :
    LocalTests outside a p u hp hm v w↔LocalArithmetic outside a p u hp hm v w := by
  simp only [LocalTests,LocalArithmetic,natAbs_eq_toNat hp0]

end Ostmann.Arithmetic.HistorySignedSupportReduction

end

end OAI
