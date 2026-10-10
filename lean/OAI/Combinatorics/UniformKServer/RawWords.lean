import Mathlib
import OAI.Combinatorics.UniformKServer.RawArithmetic

namespace OAI

                               
section

namespace UniformKServer.RawWords

def words (n : ℕ) : ℕ → List (List ℕ)
  | 0 => [[]]
  | l+1 => (List.range n).flatMap fun r => (words n l).map (r::·)

theorem mem_words (n l : ℕ) (w : List ℕ) :
    w∈words n l ↔ w.length=l ∧ ∀r∈w,r<n := by
  induction l generalizing w with
  | zero => cases w <;> simp [words]
  | succ l ih =>
    cases w with
    | nil => simp [words]
    | cons r w =>
      simp only [words,List.mem_flatMap,List.mem_map,List.cons.injEq,List.length_cons,
        Nat.succ.injEq,List.mem_range]
      constructor
      · rintro ⟨a,ha,v,hv,he,hwe⟩
        subst a;subst v
        obtain ⟨hl,hv⟩:= (ih w).mp hv
        exact ⟨hl,by simpa using And.intro ha hv⟩
      · rintro ⟨hl,hv⟩
        refine ⟨r,hv r (by simp),w,(ih w).mpr ⟨hl,?_⟩,rfl,rfl⟩
        intro q hq
        exact hv q (by simp [hq])

def upto (n H : ℕ) : List (List ℕ) := (List.range (H+1)).flatMap (words n)

theorem mem_upto (n H : ℕ) (w : List ℕ) :
    w∈upto n H ↔ w.length≤H ∧ ∀r∈w,r<n := by
  simp only [upto,List.mem_flatMap,List.mem_range,mem_words]
  constructor
  · rintro ⟨l,hl,he,hw⟩
    exact ⟨by omega,hw⟩
  · rintro ⟨hl,hw⟩
    exact ⟨w.length,by omega,rfl,hw⟩

open Primrec

theorem primitive_pow : Primrec₂ ((·^·) : ℕ→ℕ→ℕ) :=
  Primrec₂.unpaired'.1 Nat.Primrec.pow

theorem primitive_words : Primrec₂ words := by
  have h : Primrec₂ (fun n (p : ℕ × List (List ℕ)) =>
      (List.range n).flatMap fun r => p.2.map (r::·)) := by
    apply list_flatMap (list_range.comp fst)
    apply list_map ((snd.comp snd).comp fst)
    exact list_cons.comp (snd.comp fst) snd
  exact (nat_rec (const [[]]) h).of_eq (by intro n l;induction l <;> simp [words, *])

theorem primitive_upto : Primrec₂ upto := by
  unfold upto
  exact list_flatMap (list_range.comp (succ.comp snd)) (primitive_words.comp (fst.comp fst) snd)

theorem primitive_sum : Primrec (List.sum : List ℕ→ℕ) := by
  exact (list_foldr .id (const 0) (nat_add.comp (fst.comp snd) (snd.comp snd)).to₂).of_eq
    (by intro l; change l.foldr (·+·) 0=l.sum; induction l <;> simp [*])

theorem primitive_Qsum : Primrec (fun l : List RawArithmetic.Q=>l.foldr RawArithmetic.add (RawArithmetic.natural 0)) :=
  list_foldr .id (const _) (RawArithmetic.primitive_add.comp (fst.comp snd) (snd.comp snd)).to₂

end UniformKServer.RawWords

end



end OAI
