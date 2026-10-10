import Mathlib
import OAI.Combinatorics.MatchingCount.Machines.OnlineFold

namespace OAI

namespace MatchingFPRAS.OnlineTree
open TreeTyped PhysicalStream Polynomial

variable {A B : Type} [Codec A] [Codec B]

omit [Codec B] in
lemma fold_cost_bound (f : A×B→Experiment B) (t : A×B→ℕ)
    (as : List A) (b : B) (P : ℕ→B→Prop) (C M : ℕ)
    (hb : P as.length b) (hw : weight as≤M)
    (hs : ∀ a∈as,∀ k<as.length,∀ b,P (k+1) b→(f (a,b)).All (P k))
    (hc : ∀ a∈as,∀ k<as.length,∀ b,P (k+1) b→t (a,b)≤C) :
    Fold.cost f t as b≤as.length*(C+14*M+34)+10 ∧ (foldM f as b).All (P 0) := by
  induction as generalizing b with
  | nil => exact ⟨by simp [Fold.cost],hb⟩
  | cons a as ih =>
    have hwa : weight a≤M := by rw [weight_cons] at hw; omega
    have hwt : weight as≤M := by rw [weight_cons] at hw; omega
    have hb' : P (as.length+1) b := hb
    have hstep := hs a (by simp) as.length (by simp) b hb'
    have htime := hc a (by simp) as.length (by simp) b hb'
    have htt : (f (a,b)).All (fun v=>Fold.cost f t as v≤as.length*(C+14*M+34)+10 ∧
        (foldM f as v).All (P 0)) := hstep.mono (fun v hv=>ih v hv hwt
          (fun a ha k hk v hv=>hs a (by simp [ha]) k (by simp only [List.length_cons]; omega) v hv)
          (fun a ha k hk v hv=>hc a (by simp [ha]) k (by simp only [List.length_cons]; omega) v hv))
    constructor
    · have hworst := Experiment.worst_le _ _ _ (htt.mono (fun _ h=>h.1))
      change t (a,b)+6*weight a+8*weight as+34+_≤_
      simp only [List.length_cons,Nat.add_mul,Nat.one_mul]
      omega
    · rw [foldM,Experiment.all_bind]
      exact htt.mono (fun _ h=>h.2)

omit [Codec A] in
lemma all_fold_weight (f : A×B→Experiment B) (as : List A) (b : B) (C : ℕ)
    (hs : ∀ a∈as,∀ b,(f (a,b)).All (fun v=>weight v≤weight b+C)) :
    (foldM f as b).All (fun v=>weight v≤weight b+as.length*C) := by
  induction as generalizing b with
  | nil => simp [foldM,Experiment.All]
  | cons a as ih =>
    rw [foldM,Experiment.all_bind]
    exact (hs a (by simp) b).mono (fun c hc=>
      (ih c (fun a ha b=>hs a (by simp [ha]) b)).mono (fun v hv=>by
        simp only [List.length_cons,Nat.add_mul,Nat.one_mul]; omega))
end MatchingFPRAS.OnlineTree

end OAI
