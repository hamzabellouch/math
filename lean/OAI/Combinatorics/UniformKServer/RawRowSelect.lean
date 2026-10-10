import Mathlib
import OAI.Combinatorics.UniformKServer.RawExpansion
import OAI.Combinatorics.UniformKServer.RawMarks

namespace OAI

noncomputable section
                                   
section

namespace UniformKServer.RawRowSelect
open RawTyped RawTable

def partialMass (T p c : List ℕ) (r j : ℕ) : ℕ :=
  ((List.range j).map (fun i=>entry T p c r i)).sum

def choose (k : ℕ) (T p c : List ℕ) (r coin : ℕ) : ℕ :=
  RawMarks.pick ((List.range k).map (fun j=>decide (coin<partialMass T p c r (j+1))))

theorem partialMass_succ (T p c : List ℕ) (r j : ℕ) :
    partialMass T p c r (j+1)=partialMass T p c r j+entry T p c r j := by
  simp [partialMass,List.range_succ,List.map_append,List.sum_append]

theorem partialMass_mono (T p c : List ℕ) (r : ℕ) : Monotone (partialMass T p c r) := by
  apply monotone_nat_of_le_succ
  intro j
  rw [partialMass_succ]
  omega

theorem partialMass_cumulative {n k : ℕ} (T : List ℕ) (p : List (Fin n))
    (c : Configuration n k) (r : Fin n) (N : Fin k→ℕ)
    (hrep : ∀j,entry T (requests p) (config c) r.val j.val=N j) (j : Fin k) :
    partialMass T (requests p) (config c) r.val j.val=BitSampling.cumulative N j := by
  rw [partialMass,RawExpansion.range_eq_ofFn,List.map_ofFn,List.sum_ofFn]
  unfold BitSampling.cumulative
  apply Finset.sum_congr rfl
  intro i hi
  exact hrep (Fin.castLE j.isLt.le i)

theorem choose_eq {n k b : ℕ} (T : List ℕ) (p : List (Fin n))
    (c : Configuration n k) (r : Fin n) (N : Fin k→ℕ)
    (hrep : ∀j,entry T (requests p) (config c) r.val j.val=N j)
    (hN : ∑j,N j=2^b) (coins : Fin b→Bool) :
    choose k T (requests p) (config c) r.val (BitSampling.bitsEquiv b coins).val=
      (BitSampling.row N hN coins).val := by
  let j:=BitSampling.row N hN coins
  let a:=(BitSampling.bitsEquiv b coins).val
  let A:=(List.range k).map (fun i=>decide (a<partialMass T (requests p) (config c) r.val (i+1)))
  have hj : j.val<A.length := by simp [A]
  have hp:= (BitSampling.exact_row_proof N hN).2.1 coins
  have he:=partialMass_cumulative T p c r N hrep j
  have hf : A.findIdx id=j.val := by
    apply (List.findIdx_eq hj).mpr
    constructor
    · have hu : a<partialMass T (requests p) (config c) r.val (j.val+1) := by
        rw [partialMass_succ,he,hrep]
        exact hp.2
      simpa [A] using hu
    · intro i hi
      have hu : partialMass T (requests p) (config c) r.val (i+1)≤a :=
        (partialMass_mono T (requests p) (config c) r.val (by omega : i+1≤j.val)).trans (he ▸ hp.1)
      simpa [A] using Nat.not_lt_of_ge hu
  change RawMarks.pick A=j.val
  simp only [RawMarks.pick,hf,ite_eq_left hj]

section Primitive
open Primrec
variable {α : Type*} [Primcodable α]
@[fun_prop] theorem primitive_partialMass (T p c : α→List ℕ) (r j : α→ℕ)
    (hT : Primrec T) (hp : Primrec p) (hc : Primrec c) (hr : Primrec r) (hj : Primrec j) :
    Primrec (fun x=>partialMass (T x) (p x) (c x) (r x) (j x)) := by unfold partialMass;fun_prop
@[fun_prop] theorem primitive_choose (k : α→ℕ) (T p c : α→List ℕ) (r a : α→ℕ)
    (hk : Primrec k) (hT : Primrec T) (hp : Primrec p) (hc : Primrec c) (hr : Primrec r) (ha : Primrec a) :
    Primrec (fun x=>choose (k x) (T x) (p x) (c x) (r x) (a x)) := by unfold choose;fun_prop
end Primitive
end UniformKServer.RawRowSelect

end


end

end OAI
