import Mathlib
import OAI.Combinatorics.KMedian.Sparse.SparseGraphFeatures

namespace OAI

section
section
namespace MetricKMedian.SparseGraph
open Finset
variable {n m : ℕ}

def run (ν : Fin m → SparseIntegerLaw (Finset (Fin n))) : ℕ → SparseIntegerLaw (Graph n m)
  | 0 => .dirac (fun _ => ∅)
  | t+1 => if ht : t < m then step (run ν t) (ν ⟨t,ht⟩) ⟨t,ht⟩ else run ν t

def target (q : Fin n → Fin m → ℚ) (t : ℕ) (h : Fin n) (i : Fin m) : ℚ :=
  if i.val<t then q h i else 0

theorem target_succ_eq (q : Fin n → Fin m → ℚ) (t : ℕ) (ht : t < m) (h : Fin n) :
    target q (t+1) h ⟨t,ht⟩=q h ⟨t,ht⟩ := by simp [target]

theorem target_succ_ne (q : Fin n → Fin m → ℚ) (t : ℕ) (ht : t < m)
    (h : Fin n) (i : Fin m) (hi : i≠⟨t,ht⟩) : target q (t+1) h i=target q t h i := by
  have hv : i.val≠t := fun he => hi (Fin.ext he)
  have hh : i.val<t+1 ↔ i.val<t := by omega
  simp only [target,hh]

theorem run_single (ν : Fin m → SparseIntegerLaw (Finset (Fin n)))
    (q : Fin n → Fin m → ℚ)
    (hq : ∀ h i, (ν i).moment (fun S => if h∈S then 1 else 0)=q h i)
    (t : ℕ) (ht : t ≤ m) (h : Fin n) (i : Fin m) :
    (run ν t).moment (fun G => edge G h i)=target q t h i := by
  induction t with
  | zero => simp [run,SparseIntegerLaw.dirac_moment,edge,target]
  | succ t ih =>
    have htm : t < m := by omega
    rw [run,dite_eq_left htm,step_single]
    by_cases hi : i=⟨t,htm⟩
    · subst i
      rw [ite_eq_left rfl,hq,target_succ_eq]
    · rw [ite_eq_right hi,ih (by omega),target_succ_ne q t htm h i hi]

theorem run_pair (ν : Fin m → SparseIntegerLaw (Finset (Fin n)))
    (q : Fin n → Fin m → ℚ)
    (hq : ∀ h i, (ν i).moment (fun S => if h∈S then 1 else 0)=q h i)
    (t : ℕ) (ht : t ≤ m) (h l : Fin n) (i j : Fin m) (hij : i≠j) :
    (run ν t).moment (fun G => edge G h i*edge G l j)=target q t h i*target q t l j := by
  induction t with
  | zero => simp [run,SparseIntegerLaw.dirac_moment,edge,target]
  | succ t ih =>
    have htm : t < m := by omega
    rw [run,dite_eq_left htm,step_pair _ _ _ _ _ _ _ hij]
    by_cases hi : i=⟨t,htm⟩
    · have hj : j≠⟨t,htm⟩ := fun he => hij (hi.trans he.symm)
      rw [ite_eq_left hi,hq,run_single ν q hq t (by omega),
        target_succ_ne q t htm l j hj]
      subst i
      rw [target_succ_eq]
    · rw [ite_eq_right hi]
      by_cases hj : j=⟨t,htm⟩
      · rw [ite_eq_left hj,hq,run_single ν q hq t (by omega),target_succ_ne q t htm h i hi]
        subst j
        rw [target_succ_eq]
      · rw [ite_eq_right hj,ih (by omega),target_succ_ne q t htm h i hi,
          target_succ_ne q t htm l j hj]

theorem run_length (ν : Fin m → SparseIntegerLaw (Finset (Fin n))) (t : ℕ) :
    (run ν t).length ≤ n*m+(n*m)*(n*m)+1 := by
  induction t with
  | zero => change 1 ≤ _; omega
  | succ t ih =>
    rw [run]
    split_ifs with ht
    · exact ((run ν t).prodCompress_spec (ν ⟨t,ht⟩)
        (fun G S => next G S ⟨t,ht⟩) features).1
    · exact ih

theorem run_columns (ν : Fin m → SparseIntegerLaw (Finset (Fin n)))
    (P : Fin m → Finset (Fin n) → Prop)
    (hP : ∀ i, ∀ a : Fin (ν i).length, P i (ν i).states[a.val]) (t : ℕ) (ht : t ≤ m) :
    ∀ a : Fin (run ν t).length, ∀ i, i.val<t → P i ((run ν t).states[a.val] i) := by
  induction t with
  | zero => intro a i hi; omega
  | succ t ih =>
    have htm : t < m := by omega
    have he : run ν (t+1)=step (run ν t) (ν ⟨t,htm⟩) ⟨t,htm⟩ := by
      rw [run,dite_eq_left htm]
    let inv : SparseIntegerLaw (Graph n m) → Prop := fun μ =>
      ∀ a : Fin μ.length, ∀ i, i.val<t+1 → P i (μ.states[a.val] i)
    change inv (run ν (t+1))
    rw [he]
    intro a i hi
    obtain ⟨j,k,hjk⟩ := ((run ν t).prodCompress_spec (ν ⟨t,htm⟩)
      (fun G S => next G S ⟨t,htm⟩) features).2.1 a
    change (step (run ν t) (ν ⟨t,htm⟩) ⟨t,htm⟩).states[a.val]=_ at hjk
    rw [hjk]
    by_cases hi' : i=⟨t,htm⟩
    · subst i
      simpa only [next,Function.update_self] using hP ⟨t,htm⟩ k
    · have hiv : i.val≠t := fun h => hi' (Fin.ext h)
      simpa only [next,Function.update_of_ne hi'] using ih (by omega) j i (by omega)

end MetricKMedian.SparseGraph
end
end

end OAI
