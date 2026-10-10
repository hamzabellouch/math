import Mathlib
import OAI.Computability.QuantumFactoring.EmissionCombinators

namespace OAI



section
namespace ExactQuantumFactoring.NetworkEmission
open BooleanNetwork BitStackProgram BitStackProgram.Emits
structure FilterState (k : ℕ) (w : ℕ→ℕ) where
  depth : ℕ
  raw : BooleanNetwork k (w depth)
  pending : List (BooleanNetwork k 1)
def filterStep {k : ℕ} {w : ℕ→ℕ} (prev : ∀s,BooleanNetwork (w (s+1)) (w s))
    (keep : ∀s,BooleanNetwork k (w (s+1))→BooleanNetwork k 1) : FilterState k w→FilterState k w
  | ⟨0,v,ps⟩ => ⟨0,v,ps⟩
  | ⟨s+1,v,ps⟩ => ⟨s,v.comp (prev s),keep s v::ps⟩
def FilterState.code {k : ℕ} {w : ℕ→ℕ} (s : FilterState k w) : ℕ×Pack×List Pack:=
  (s.depth,erasePack s.raw,s.pending.map erasePack)
def filterPrefix {k : ℕ} {w : ℕ→ℕ} (prev : ∀s,BooleanNetwork (w (s+1)) (w s))
    (keep : ∀s,BooleanNetwork k (w (s+1))→BooleanNetwork k 1) : ∀s,BooleanNetwork k (w s)→BooleanNetwork k 1
  | 0,_=>BooleanNetwork.constant true
  | s+1,v=>(filterPrefix prev keep s (v.comp (prev s))).band (keep s v)
lemma filterStep_depth {k : ℕ} {w : ℕ→ℕ} (prev : ∀s,BooleanNetwork (w (s+1)) (w s))
    (keep : ∀s,BooleanNetwork k (w (s+1))→BooleanNetwork k 1) (s : FilterState k w) :
    (filterStep prev keep s).depth=s.depth-1:=by cases s with | mk d v ps=>cases d <;> rfl
lemma filterRun_depth {k : ℕ} {w : ℕ→ℕ} (prev : ∀s,BooleanNetwork (w (s+1)) (w s))
    (keep : ∀s,BooleanNetwork k (w (s+1))→BooleanNetwork k 1) (s : FilterState k w) (i : ℕ) :
    ((filterStep prev keep)^[i] s).depth=s.depth-i:=by
  induction i with
  | zero=>simp
  | succ i ih=>rw [Function.iterate_succ_apply',filterStep_depth,ih,Nat.sub_sub]
lemma filterStep_value {k : ℕ} {w : ℕ→ℕ} (prev : ∀s,BooleanNetwork (w (s+1)) (w s))
    (keep : ∀s,BooleanNetwork k (w (s+1))→BooleanNetwork k 1) (s : FilterState k w) :
    (filterStep prev keep s).pending.foldl BooleanNetwork.band
      (filterPrefix prev keep (filterStep prev keep s).depth (filterStep prev keep s).raw)=
    s.pending.foldl BooleanNetwork.band (filterPrefix prev keep s.depth s.raw):=by
  cases s with | mk d v ps=>cases d <;> rfl
lemma filterRun_value {k : ℕ} {w : ℕ→ℕ} (prev : ∀s,BooleanNetwork (w (s+1)) (w s))
    (keep : ∀s,BooleanNetwork k (w (s+1))→BooleanNetwork k 1) (s : FilterState k w) (i : ℕ) :
    ((filterStep prev keep)^[i] s).pending.foldl BooleanNetwork.band
      (filterPrefix prev keep ((filterStep prev keep)^[i] s).depth ((filterStep prev keep)^[i] s).raw)=
    s.pending.foldl BooleanNetwork.band (filterPrefix prev keep s.depth s.raw):=by
  induction i with
  | zero=>rfl
  | succ i ih=>rw [Function.iterate_succ_apply',filterStep_value,ih]
lemma filterRun_result {k : ℕ} {w : ℕ→ℕ} (prev : ∀s,BooleanNetwork (w (s+1)) (w s))
    (keep : ∀s,BooleanNetwork k (w (s+1))→BooleanNetwork k 1) (s : ℕ) (v : BooleanNetwork k (w s)) :
    ((filterStep prev keep)^[s] ⟨s,v,[]⟩).pending.foldl BooleanNetwork.band (BooleanNetwork.constant true)=
      filterPrefix prev keep s v:=by
  have h:=filterRun_value prev keep (⟨s,v,[]⟩ : FilterState k w) s
  have hd:=filterRun_depth prev keep (⟨s,v,[]⟩ : FilterState k w) s
  dsimp only at hd
  rw [Nat.sub_self] at hd
  generalize he : ((filterStep prev keep)^[s] ⟨s,v,[]⟩)=r at *
  cases r with | mk d a ps=>
    dsimp only [FilterState.depth] at hd
    subst d
    exact h
lemma filterRun_bounds {k : ℕ} {w : ℕ→ℕ} (prev : ∀s,BooleanNetwork (w (s+1)) (w s))
    (keep : ∀s,BooleanNetwork k (w (s+1))→BooleanNetwork k 1)
    (hp : ∀s,(prev s).net.count=0) (S B C : ℕ)
    (hc : ∀s,S>s→∀v: BooleanNetwork k (w (s+1)),v.net.count≤B→(keep s v).net.count≤C)
    (v : BooleanNetwork k (w S)) (hv : v.net.count≤B) (i : ℕ) :
    let r := ((filterStep prev keep)^[i] ⟨S,v,[]⟩);
    r.depth ≤ S ∧ r.raw.net.count ≤ B ∧ r.pending.length ≤ i ∧ (∀ a ∈ r.pending, a.net.count ≤ C) := by
  induction i with
  | zero=>exact ⟨le_rfl,hv,le_rfl,by simp⟩
  | succ i ih=>
    rw [Function.iterate_succ_apply']
    generalize he : ((filterStep prev keep)^[i] ⟨S,v,[]⟩)=r at *
    rcases ih with ⟨hd,hv,hl,hc'⟩
    cases r with | mk d a ps=>
      cases d with
      | zero=>exact ⟨hd,hv,hl.trans (by omega),hc'⟩
      | succ d=>
        dsimp only [FilterState.depth,FilterState.raw,FilterState.pending] at hd hv hl hc'
        refine ⟨by dsimp only [filterStep];omega,?_,?_,?_⟩
        · simpa only [filterStep,BooleanNetwork.count_comp,hp,Nat.add_zero] using hv
        · dsimp only [filterStep];simp only [List.length_cons];omega
        · intro a ha
          rcases List.mem_cons.mp ha with h|h
          · subst a;exact hc d (by omega) _ hv
          · exact hc' a h
end ExactQuantumFactoring.NetworkEmission

end



end OAI
