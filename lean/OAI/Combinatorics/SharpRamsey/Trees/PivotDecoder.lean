import Mathlib
import OAI.Combinatorics.SharpRamsey.Trees.PivotBanks

namespace OAI

section
namespace SharpLogRamsey.ActualPivot
open Finset Real Incidence Validation Selection ScheduledBanks PublicTables
  ReadyTests PivotGeometry ProjectiveDuality TreeDecoder
open scoped Classical BigOperators
noncomputable section
variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]
  [Fintype (Projectivization K V)] [Fintype (Projectivization K (Module.Dual K V))]
  [Fintype (Projectivization K (Module.Dual K (Module.Dual K V)))]

abbrev FirstCode (b : ℝ) := Σ a : Address (Projectivization K V)
  (Projectivization K (Module.Dual K V)), Fin (cutoff (Nat.card K) (b+log 1000000) a)
abbrev SecondCode (b : ℝ) := Σ a : Address (Projectivization K (Module.Dual K V))
  (Projectivization K (Module.Dual K (Module.Dual K V))),
  Fin (cutoff (Nat.card K) (b+log 1000000) a)
abbrev Code (b : ℝ) := FirstCode (K:=K) (V:=V) b × SecondCode (K:=K) (V:=V) b

def read (b : ℝ) (z : FirstBank (K:=K) (V:=V) b) (w : SecondBank (K:=K) (V:=V) b) :
    CapReader (Projectivization K V) (Projectivization K (Module.Dual K V)) (Code (K:=K) (V:=V) b) :=
  fun U c => (primalCap U.1 (rowAt _ (w c.2.1) c.2.2),
    cap SharpLogRamsey.Incidence.Incident (Nat.card K) U.2 (rowAt _ (z c.1.1) c.1.2))

variable {n : ℕ} {A : Finset (Projectivization K V)}
  {B : Finset (Projectivization K (Module.Dual K V))} {b : ℝ}

def Input.choose (d : Input n A B b) (hdim : Module.finrank K V=n+3)
    (z : FirstBank (K:=K) (V:=V) b) (w : SecondBank (K:=K) (V:=V) b) : Option (Code (K:=K) (V:=V) b) :=
  match hi : d.firstCall.bankIndex (b+log 1000000) n z with
  | none => none
  | some i =>
    let r := rowAt _ (z d.firstCall.address) i
    let c := d.secondCall hdim r (index_valid _ _ _ i hi)
    (c.bankIndex (b+log 1000000) n w).map (fun j => (⟨d.firstCall.address,i⟩,⟨c.address,j⟩))

omit [Finite K] [FiniteDimensional K V]
  [Fintype (Projectivization K (Module.Dual K (Module.Dual K V)))] in
lemma Input.firstRow_eq (d : Input n A B b) (z : FirstBank (K:=K) (V:=V) b) :
    d.firstCall.bankRow (b+log 1000000) n z =
      (d.firstCall.bankIndex (b+log 1000000) n z).map (rowAt _ (z d.firstCall.address)) := by
  exact (reconstruct_first _ _ _).symm

lemma Input.next_of_index (d : Input n A B b) (hdim : Module.finrank K V=n+3)
    (z : FirstBank (K:=K) (V:=V) b)
    (i : Fin (cutoff (Nat.card K) (b+log 1000000) d.firstCall.address))
    (hi : d.firstCall.bankIndex (b+log 1000000) n z=some i) :
    d.next hdim z=some (d.secondCall hdim (rowAt _ (z d.firstCall.address) i)
      (index_valid _ _ _ i hi)) := by
  have hr : d.firstCall.bankRow (b+log 1000000) n z=some (rowAt _ (z d.firstCall.address) i) := by
    rw [d.firstRow_eq,hi,Option.map_some]
  unfold Input.next
  split
  · rename_i he
    rw [he] at hr
    cases hr
  · rename_i r he
    have hrow := Option.some.inj (he.symm.trans hr)
    subst r
    rfl

lemma Input.choose_of_index (d : Input n A B b) (hdim : Module.finrank K V=n+3)
    (z : FirstBank (K:=K) (V:=V) b) (w : SecondBank (K:=K) (V:=V) b)
    (i : Fin (cutoff (Nat.card K) (b+log 1000000) d.firstCall.address))
    (hi : d.firstCall.bankIndex (b+log 1000000) n z=some i) :
    d.choose hdim z w =
      let c := d.secondCall hdim (rowAt _ (z d.firstCall.address) i) (index_valid _ _ _ i hi)
      (c.bankIndex (b+log 1000000) n w).map (fun j=>(⟨d.firstCall.address,i⟩,⟨c.address,j⟩)) := by
  unfold Input.choose
  split
  · rename_i he
    rw [he] at hi
    cases hi
  · rename_i j he
    have hij := Option.some.inj (he.symm.trans hi)
    subst j
    rfl

lemma Input.choose_first_fail (d : Input n A B b) (hdim : Module.finrank K V=n+3)
    (z : FirstBank (K:=K) (V:=V) b) (w : SecondBank (K:=K) (V:=V) b)
    (hi : d.firstCall.bankIndex (b+log 1000000) n z=none) : d.choose hdim z w=none := by
  unfold Input.choose
  split
  · rfl
  · rename_i j he
    rw [hi] at he
    cases he

lemma Input.choose_failure (d : Input n A B b) (hdim : Module.finrank K V=n+3)
    (z : FirstBank (K:=K) (V:=V) b) (w : SecondBank (K:=K) (V:=V) b) :
    (if d.choose hdim z w=none then (1:ℝ) else 0)=d.failure hdim z w := by
  cases hi : d.firstCall.bankIndex (b+log 1000000) n z with
  | none =>
    have hr : d.firstCall.bankRow (b+log 1000000) n z=none := by
      rw [d.firstRow_eq,hi,Option.map_none]
    have hn := (d.next_none hdim z).mpr hr
    rw [d.choose_first_fail hdim z w hi]
    simp only [Input.failure,hn,Option.elim_none,ite_true]
  | some i =>
    let c := d.secondCall hdim (rowAt _ (z d.firstCall.address) i) (index_valid _ _ _ i hi)
    have hn : d.next hdim z=some c := d.next_of_index hdim z i hi
    have hr : c.bankRow (b+log 1000000) n w =
        (c.bankIndex (b+log 1000000) n w).map (rowAt _ (w c.address)) :=
      (reconstruct_first _ _ _).symm
    rw [d.choose_of_index hdim z w i hi]
    simp only [Input.failure,hn,Option.elim_some]
    change (if (c.bankIndex (b+log 1000000) n w).map _=none then (1:ℝ) else 0)=_
    rw [hr]
    cases c.bankIndex (b+log 1000000) n w <;> simp

theorem Input.choose_failure_bound (d : Input n A B b) (hdim : Module.finrank K V=n+3) :
    (∑ z, (bankLaw (Nat.card K) (b+log 1000000)).mass z *
      ∑ w, (bankLaw (Nat.card K) (b+log 1000000)).mass w *
        (if d.choose hdim z w=none then 1 else 0)) ≤ 2*exp (-(Nat.card K:ℝ)) := by
  simp_rw [d.choose_failure hdim]
  exact d.failure_bound hdim

theorem Input.choose_valid (d : Input n A B b) (hdim : Module.finrank K V=n+3)
    (z : FirstBank (K:=K) (V:=V) b) (w : SecondBank (K:=K) (V:=V) b)
    (c : Code (K:=K) (V:=V) b) (hc : d.choose hdim z w=some c) :
    let D := read b z w (d.U,d.UT) c
    D.1⊆d.U ∧ D.2⊆d.UT ∧
    (D.1.card:ℝ)≤2000*(Nat.card K:ℝ)^(n+3)/B.card ∧
    (D.2.card:ℝ)≤2000*(Nat.card K:ℝ)^(n+3)/A.card ∧
    (99:ℝ)*(A∩d.U).card≤100*((A∩d.U)∩D.1).card ∧
    (99:ℝ)*(B∩d.UT).card≤100*((B∩d.UT)∩D.2).card := by
  unfold Input.choose at hc
  split at hc
  · cases hc
  · rename_i i hi
    let r := rowAt _ (z d.firstCall.address) i
    have hv : d.firstCall.accept n r := index_valid _ _ _ i hi
    let c' := d.secondCall hdim r hv
    change (c'.bankIndex (b+log 1000000) n w).map _=some c at hc
    obtain ⟨j,hj,he⟩ := Option.map_eq_some_iff.mp hc
    subst c
    have hu := index_valid (c'.accept n) _ (w c'.address) j hj
    exact accepted_caps A d.U d.W B d.UT r (rowAt _ (w c'.address) j) hv hu

end
end SharpLogRamsey.ActualPivot

end

end OAI
