import Mathlib
import OAI.Combinatorics.KMedian.Compression.GaussianListSize
import OAI.Combinatorics.KMedian.Compression.GaussianListPivot

namespace OAI


                                             
section
namespace MetricKMedian.Gaussian.ListOperation
open Binary Finset

def desc (r n : ℕ) (A : RatMatrix r n) (fs : Frames) : State :=
  .inl ((List.replicate n (),matrix (values A)),fs)
def returned (r n : ℕ) (A : RatMatrix r n) (fs : Frames) : State :=
  .inr (kernelList r n A,fs)

 theorem down_base (n : ℕ) (A : RatMatrix 0 n) (fs : Frames) :
    body (desc 0 n A fs)=.inr (returned 0 n A fs) := by
  simp only [desc,body,Sum.elim_inl,down,matrix,List.ofFn_zero,List.isEmpty_nil,ite_true]
  rw [basis_ofFn]
  simp only [returned,kernelList,kernelVector,Vector.getElem_ofFn]

 theorem down_pivot {r n : ℕ} (A : RatMatrix (r+1) (n+1)) (fs : Frames)
    (h : (univ.filter (fun j => values A 0 j ≠ 0)).Nonempty) :
    let p := (univ.filter (fun j => values A 0 j ≠ 0)).min' h
    body (desc (r+1) (n+1) A fs)=
      .inr (desc r n (tabulate (Gaussian.residual (values A) p)) ((p.val,List.ofFn (values A 0))::fs)) := by
  dsimp only
  let p := (univ.filter (fun j => values A 0 j ≠ 0)).min' h
  have hm : matrix (values A)=List.ofFn (values A 0)::matrix (fun i : Fin r => values A i.succ) := List.ofFn_succ
  simp only [desc,body,Sum.elim_inl,down,hm,List.isEmpty_cons,Bool.false_eq_true,ite_false,List.replicate_succ,List.head?_cons,Option.getD_some,List.tail_cons]
  simp only [pivot_ofFn _ h,List.length_ofFn,residual_matrix,values_tabulate]
  exact ite_eq_left p.isLt

 theorem down_skip {r n : ℕ} (A : RatMatrix (r+1) (n+1)) (fs : Frames)
    (h : ¬(univ.filter (fun j => values A 0 j ≠ 0)).Nonempty) :
    body (desc (r+1) (n+1) A fs)=
      .inr (desc r (n+1) (tabulate (fun i j => values A i.succ j)) fs) := by
  have hm : matrix (values A)=List.ofFn (values A 0)::matrix (fun i : Fin r => values A i.succ) := List.ofFn_succ
  simp only [desc,body,Sum.elim_inl,down,hm,List.isEmpty_cons,Bool.false_eq_true,ite_false,List.replicate_succ,List.head?_cons,Option.getD_some,List.tail_cons]
  simp only [pivot_ofFn_zero _ h,List.length_ofFn,lt_self_iff_false,ite_false,values_tabulate]

 theorem return_pivot {r n : ℕ} (A : RatMatrix (r+1) (n+1)) (fs : Frames)
    (h : (univ.filter (fun j => values A 0 j ≠ 0)).Nonempty) :
    let p := (univ.filter (fun j => values A 0 j ≠ 0)).min' h
    body (returned r n (tabulate (Gaussian.residual (values A) p)) ((p.val,List.ofFn (values A 0))::fs))=
      .inr (returned (r+1) (n+1) A fs) := by
  dsimp only
  simp only [returned,body,Sum.elim_inr,up,List.isEmpty_cons,Bool.false_eq_true,ite_false,List.head?_cons,Option.getD_some,List.tail_cons]
  simp only [kernelList,lift_ofFn,kernelVector,dite_eq_left h,Vector.getElem_ofFn]

 theorem return_skip {r n : ℕ} (A : RatMatrix (r+1) (n+1)) (fs : Frames)
    (h : ¬(univ.filter (fun j => values A 0 j ≠ 0)).Nonempty) :
    returned r (n+1) (tabulate (fun i j => values A i.succ j)) fs=returned (r+1) (n+1) A fs := by
  simp only [returned,kernelList,kernelVector,dite_eq_right h]

 theorem finish (r n : ℕ) (A : RatMatrix r n) :
    body (returned r n A [])=.inl (kernelList r n A) := rfl

 theorem audit_pivot {R N H K r n : ℕ} {A : RatMatrix (r+1) (n+1)}
    (ha : Audit R N H K (r+1) (n+1) A)
    (h : (univ.filter (fun j => values A 0 j ≠ 0)).Nonempty) :
    Audit R N H K r n (tabulate (Gaussian.residual (values A) ((univ.filter (fun j => values A 0 j ≠ 0)).min' h))) := by
  intro B hB
  apply ha B
  simp only [kernelStates,dite_eq_left h,List.mem_cons]
  exact Or.inr hB

 theorem audit_skip {R N H K r n : ℕ} {A : RatMatrix (r+1) (n+1)}
    (ha : Audit R N H K (r+1) (n+1) A)
    (h : ¬(univ.filter (fun j => values A 0 j ≠ 0)).Nonempty) :
    Audit R N H K r (n+1) (tabulate (fun i j => values A i.succ j)) := by
  intro B hB
  apply ha B
  simp only [kernelStates,dite_eq_right h,List.mem_cons]
  exact Or.inr hB
end MetricKMedian.Gaussian.ListOperation
end

end OAI
