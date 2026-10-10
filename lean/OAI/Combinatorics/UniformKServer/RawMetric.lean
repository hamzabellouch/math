import Mathlib
import OAI.Combinatorics.UniformKServer.RawCertificate
import OAI.Combinatorics.UniformKServer.Epochs
import OAI.Combinatorics.UniformKServer.RawTyped
import OAI.Combinatorics.UniformKServer.FiniteRepresentation

namespace OAI

noncomputable section
                                
section

namespace UniformKServer.RawMetric
open RawArithmetic RawWords RawTable RawTyped RawCertificate

def present (a : ℚ) : Q := (a.num.natAbs,a.den-1)
@[simp] theorem present_eq (a : ℚ) (ha : 0≤a) : value (present a)=a := eq_present a ha

theorem present_pos (a : ℚ) (ha : 0<a) : 0<(present a).1 := by
  change 0<a.num.natAbs
  exact Int.natAbs_pos.mpr (ne_of_gt (Rat.num_pos.mpr ha))

theorem metric_key_inj {n : ℕ} : Function.Injective (fun p : Fin n×Fin n=>p.1.val*n+p.2.val) := by
  intro p q hpq
  have hy:=congrArg (fun z=>z%n) hpq
  have hy' : p.2.val=q.2.val := by simpa [Nat.add_mod,Nat.mod_eq_of_lt p.2.isLt,Nat.mod_eq_of_lt q.2.isLt] using hy
  change p.1.val*n+p.2.val=q.1.val*n+q.2.val at hpq
  have hx : p.1.val*n=q.1.val*n := by omega
  have hn : 0<n := Nat.zero_lt_of_lt p.1.isLt
  exact Prod.ext (Fin.ext (Nat.eq_of_mul_eq_mul_right hn hx)) (Fin.ext hy')

theorem represents {n : ℕ} (d : RationalMetric n) : ∃draw : List Q,
    ∀x y : Fin n,value (dist n draw x.val y.val)=d.distance x y := by
  obtain ⟨draw,hd⟩:=FiniteRepresentation.represents (fun p : Fin n×Fin n=>p.1.val*n+p.2.val)
    metric_key_inj (fun p=>present (d.distance p.1 p.2)) (natural 0)
  refine ⟨draw,?_⟩
  intro x y
  rw [RawTable.dist,hd (x,y),present_eq _ (d.nonneg x y)]

theorem bounds_ok {n : ℕ} (d : RationalMetric n) (draw : List Q)
    (hd : ∀x y : Fin n,value (dist n draw x.val y.val)=d.distance x y)
    (D δ : Q) (hdiam : ∀x y,d.distance x y≤value D)
    (hsep : ∀x y,x≠y→value δ≤d.distance x y) : boundsOK n draw D δ=true := by
  apply List.all_eq_true.mpr
  intro x hx
  apply List.all_eq_true.mpr
  intro y hy
  let x' : Fin n := ⟨x,List.mem_range.mp hx⟩
  let y' : Fin n := ⟨y,List.mem_range.mp hy⟩
  apply Bool.and_eq_true_iff.mpr
  refine ⟨decide_eq_true ((le_iff _ _).mpr (by
    change value (dist n draw x'.val y'.val)≤value D
    rw [hd];exact hdiam x' y')),?_⟩
  by_cases h : x=y
  · simp [h]
  · have h' : x'≠y' := fun he=>h (congrArg Fin.val he)
    have hs:=hsep x' y' h'
    have hl : le δ (dist n draw x y) := (le_iff _ _).mpr (by
      change value δ≤value (dist n draw x'.val y'.val)
      rw [hd];exact hs)
    simp [hl]

theorem horizon_eq (k M : ℕ) : RawCertificate.horizon k M=UniformKServer.horizon k M := by
  unfold RawCertificate.horizon UniformKServer.horizon
  have h : ∀m,(List.map (fun i=>k^i) (List.range m)).sum=∑i∈Finset.range m,k^i := by
    intro m
    induction m with
    | zero=>simp
    | succ m ih=>simp [List.range_succ,Finset.sum_range_succ,ih]
  exact h _

end UniformKServer.RawMetric

end


end

end OAI
