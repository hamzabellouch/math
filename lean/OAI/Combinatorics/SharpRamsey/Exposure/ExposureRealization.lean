import Mathlib
import OAI.Combinatorics.SharpRamsey.Exposure.ExposureModel

namespace OAI

section
namespace SharpLogRamsey.Selection
open Finset
open scoped Classical BigOperators
noncomputable section
variable {β C : Type} [Fintype β] [Fintype C]
namespace ExposureModel

def atRound (n : ℕ) : (k : ℕ)→{ι : Type}→ [Fintype ι] →  [DecidableEq ι] →
    Law (ι→β)→(C×Fin (n+k)↪ι)→(ι→Option C)→Fin k→ExposureModel ι β C
  | 0,_,_,_,_,_,_,j => Fin.elim0 j
  | k+1,_,_,_,p,e,own,j => Fin.cases (initial p e own)
    (fun t=>join p e (fun f z=>
      atRound n k ((p.cond (fun y (i:freshRepresentatives e f)=>y i) z).restrict
        (freshRepresentatives e f)ᶜ) (remainingEmbedding e f) (fun i=>own i) t)) j

theorem atRound_preserves (n k : ℕ) {ι : Type} [Fintype ι] [DecidableEq ι]
    (p : Law (ι→β)) (e : C×Fin (n+k)↪ι) (own : ι→Option C) (t : Fin k)
    (φ : (ι→β)→ℝ) : (atRound n k p e own t).expectation φ=∑ y,p.mass y*φ y := by
  induction k generalizing ι with
  | zero => exact Fin.elim0 t
  | succ k ih =>
    refine Fin.cases ?_ (fun j=>?_) t
    · exact initial_expectation p e own φ
    · apply join_preserves
      intro f z ψ
      exact ih _ (remainingEmbedding e f) (fun i=>own i) j ψ

theorem atRound_remaining (n k : ℕ) {ι : Type} [Fintype ι] [DecidableEq ι]
    (p : Law (ι→β)) (e : C×Fin (n+k)↪ι) (own : ι→Option C) (t : Fin k)
    (z : (atRound n k p e own t).History) :
    n≤(atRound n k p e own t).remaining z := by
  induction k generalizing ι with
  | zero => exact Fin.elim0 t
  | succ k ih =>
    induction t using Fin.cases with
    | zero => change n≤n+(k+1); omega
    | succ j => exact ih _ (remainingEmbedding e z.1) (fun i=>own i) j z.2.2

theorem atRound_owner (n k : ℕ) {ι : Type} [Fintype ι] [DecidableEq ι]
    (p : Law (ι→β)) (e : C×Fin (n+k)↪ι) (own : ι→Option C) (t : Fin k)
    (z : (atRound n k p e own t).History) (i : (atRound n k p e own t).Index z) :
    (atRound n k p e own t).owner z i=own ((atRound n k p e own t).origin z i) := by
  induction k generalizing ι with
  | zero => exact Fin.elim0 t
  | succ k ih =>
    induction t using Fin.cases with
    | zero => rfl
    | succ j => exact ih _ (remainingEmbedding e z.1) (fun i=>own i) j z.2.2 i

theorem atRound_embedding_owner (n k : ℕ) {ι : Type} [Fintype ι] [DecidableEq ι]
    (p : Law (ι→β)) (e : C×Fin (n+k)↪ι) (own : ι→Option C)
    (hown : ∀ b x,own (e (b,x))=some b) (t : Fin k)
    (z : (atRound n k p e own t).History) (b : C)
    (x : Fin ((atRound n k p e own t).remaining z)) :
    (atRound n k p e own t).owner z ((atRound n k p e own t).embedding z (b,x))=some b := by
  induction k generalizing ι with
  | zero => exact Fin.elim0 t
  | succ k ih =>
    induction t using Fin.cases with
    | zero => exact hown b x
    | succ j =>
      exact ih _ (remainingEmbedding e z.1) (fun i=>own i)
        (remaining_own e z.1 own hown) j z.2.2 x

theorem atRound_unowned (n k : ℕ) {ι : Type} [Fintype ι] [DecidableEq ι]
    (p : Law (ι→β)) (e : C×Fin (n+k)↪ι) (own : ι→Option C)
    (hown : ∀ b x,own (e (b,x))=some b) (t : Fin k)
    (z : (atRound n k p e own t).History) (i : ι) (hi : own i=none) :
    ∃ j,(atRound n k p e own t).origin z j=i := by
  induction k generalizing ι with
  | zero => exact Fin.elim0 t
  | succ k ih =>
    induction t using Fin.cases with
    | zero => exact ⟨i,rfl⟩
    | succ j =>
      have hn : i∉freshRepresentatives e z.1 := by
        intro hh
        obtain ⟨b,_,hb⟩:=mem_image.mp hh
        have hh:=hown b (z.1 b)
        rw [hb,hi] at hh
        cases hh
      obtain ⟨v,hv⟩ := ih _ (remainingEmbedding e z.1) (fun i=>own i)
        (remaining_own e z.1 own hown) j z.2.2 ⟨i,mem_compl.mpr hn⟩ hi
      exact ⟨v,congrArg Subtype.val hv⟩

end ExposureModel
end
end SharpLogRamsey.Selection

end

end OAI
