import Mathlib
import OAI.Combinatorics.MatchingCount.Machines.OnlineFold

namespace OAI

namespace MatchingFPRAS.OnlineWord
open PhysicalStream TreeData TreeFunction TreeTyped OnlineTree

def prepend : ℕ → List Bool → Experiment (List Bool)
  | 0,acc => .done acc
  | n+1,acc => .read (fun b=>prepend n (b::acc))
lemma mean_prepend (n : ℕ) (acc : List Bool) (f : List Bool → ℚ) :
    (prepend n acc).mean f=(Experiment.word n).mean (fun w=>f ((List.ofFn w).reverse++acc)) := by
  induction n generalizing acc with
  | zero => simp [prepend,Experiment.word,Experiment.mean]
  | succ n ih =>
    simp only [prepend,Experiment.word,Experiment.mean,Experiment.mean_map,ih]
    congr 2 <;> congr 1 <;> funext w <;>
      simp [List.ofFn_succ,List.reverse_cons,List.append_assoc]

def reverseBits (n : ℕ) : Bits n ≃ Bits n where
  toFun w i:=w i.rev
  invFun w i:=w i.rev
  left_inv w:=by funext i; simp
  right_inv w:=by funext i; simp
lemma ofFn_reverse (n : ℕ) (w : Bits n) :
    List.ofFn (reverseBits n w)=(List.ofFn w).reverse := by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp only [List.length_ofFn] at hi hj
    simp only [reverseBits,Equiv.coe_fn_mk,List.getElem_ofFn,List.getElem_reverse,Fin.rev,List.length_ofFn]
    congr 1
    apply Fin.ext
    change n-(i+1)=n-1-i
    omega
lemma average_reverse (n : ℕ) (f : List Bool → ℚ) :
    average (fun w : Bits n=>f (List.ofFn w).reverse)=average (fun w : Bits n=>f (List.ofFn w)) := by
  unfold average
  congr 1
  exact Fintype.sum_equiv (reverseBits n) _ _ (fun w=>by rw [ofFn_reverse])
lemma mean_prepend_nil (n : ℕ) (f : List Bool → ℚ) :
    (prepend n []).mean f=average (fun w : Bits n=>f (List.ofFn w)) := by
  rw [mean_prepend,Experiment.mean_word]
  simp only [List.append_nil]
  exact average_reverse n f

def step (x : ℕ×List Bool) : Experiment (List Bool) := .read (fun b=>.done (b::x.2))
noncomputable def stepRealizer : OnlineTree.Realizer step :=
  (OnlineTree.choose
    (OnlineTree.deterministic (TreeTyped.composition (TreeTyped.pair (TreeTyped.constant false) TreeTyped.second) TreeTyped.listCons))
    (OnlineTree.deterministic (TreeTyped.composition (TreeTyped.pair (TreeTyped.constant true) TreeTyped.second) TreeTyped.listCons))).congr
    (by intro x f; rfl)
lemma fold_step (as : List ℕ) (acc : List Bool) :
    OnlineTree.foldM step as acc=prepend as.length acc := by
  induction as generalizing acc with
  | nil => rfl
  | cons a as ih => simp only [OnlineTree.foldM,step,Experiment.bind,ih,List.length_cons,prepend]

noncomputable def listRealizer : OnlineTree.Realizer (fun as : List ℕ=>prepend as.length []) :=
  (OnlineTree.composition
    (OnlineTree.deterministic (TreeTyped.pair (TreeTyped.identity (A:=List ℕ)) (TreeTyped.constant ([] : List Bool))))
    (OnlineTree.fold stepRealizer)).congr (by
      intro as f
      change (OnlineTree.foldM step as []).mean f=(prepend as.length []).mean f
      rw [fold_step])

noncomputable def naturalRealizer : OnlineTree.Realizer (fun n : ℕ=>prepend n []) :=
  (OnlineTree.composition (OnlineTree.deterministic TreeTyped.range) listRealizer).congr
    (by intro n f; simp only [Experiment.mean_bind,Experiment.mean,List.length_range])

lemma all_length (n : ℕ) (acc : List Bool) :
    (prepend n acc).All (fun bs=>bs.length=n+acc.length) := by
  induction n generalizing acc with
  | zero => simp only [prepend,Experiment.All,Nat.zero_add]
  | succ n ih =>
    change (prepend n (false::acc)).All _ ∧ (prepend n (true::acc)).All _
    constructor <;> exact (ih _).mono (fun bs h=>by simp only [List.length_cons] at h; omega)
end MatchingFPRAS.OnlineWord

end OAI
