import OAI.Computability.MatchingCount.SelectRoutine

namespace OAI

section

namespace BinaryMatching.StackCode
open Polynomial

def unary (n : ℕ) : List Bool := List.replicate n true
@[simp] lemma unary_length (n : ℕ) : (unary n).length=n := by simp [unary]
@[simp] lemma unary_reverse (n : ℕ) : (unary n).reverse=unary n := by simp [unary]
@[simp] lemma unary_zero : unary 0=[] := rfl
@[simp] lemma unary_succ (n : ℕ) : unary (n+1)=true::unary n := by simp [unary,List.replicate_succ]

namespace Routine
variable {α : Type} {ea : α → List Bool} {f : α → α}

lemma iterate_runs_at (p : Routine ea ea f) {R : ℕ}
    (ι : Fin (p.scratch+1) → Fin R) (hι : Function.Injective ι)
    (counter : Fin R) (hc : ∀ i,ι i≠counter) (B n : ℕ) (a : α) (s : Store R)
    (hin : s (ι 0)=ea a) (hclean : ∀ i,i≠0 → s (ι i)=[]) (hcount : s counter=unary n)
    (hb : ∀ j≤n,(ea (f^[j] a)).length≤B) :
    ∃ t≤n*(p.time.eval B+2)+1,
      (Block.loop counter ((Block.pop counter).seq (p.block.rename ι))).Runs s
        (Function.update (Function.update s counter []) (ι 0) (ea (f^[n] a))) t := by
  induction n generalizing a s with
  | zero =>
    have he : Function.update (Function.update s counter []) (ι 0) (ea (f^[0] a))=s := by
      simp only [Function.iterate_zero, id_eq]
      have hc0 : s counter=[] := hcount
      rw [←hin,←hc0,Function.update_eq_self,Function.update_eq_self]
    rw [he]
    exact ⟨1,by simp,Block.loop_runs_empty _ _ _ (by simpa using hcount)⟩
  | succ n ih =>
    let s₁ := Function.update s counter (unary n)
    let s₂ := Function.update s₁ (ι 0) (ea (f a))
    have hp : (Block.pop counter).Runs s s₁ 1 := by
      simpa [s₁,hcount] using Block.pop_runs counter s
    obtain ⟨t,ht,hp₀⟩ := p.run_at ι hι s₁ a (by simpa [s₁,hc] using hin) (by
      intro i hi
      simpa [s₁,hc] using hclean i hi)
    change (p.block.rename ι).Runs s₁ s₂ t at hp₀
    obtain ⟨u,hu,hi⟩ := ih (f a) s₂ (by simp [s₂]) (by
      intro i hi
      have hne : ι i≠ι 0 := fun h => hi (hι h)
      simp [s₂,s₁,Function.update_of_ne hne,hc,hclean i hi])
      (by simp [s₂,s₁,(hc 0).symm]) (by
        intro j hj
        simpa only [Function.iterate_succ_apply] using hb (j+1) (by omega))
    have he : Function.update (Function.update s₂ counter []) (ι 0) (ea (f^[n] (f a)))=
        Function.update (Function.update s counter []) (ι 0) (ea (f^[n+1] a)) := by
      funext k
      by_cases hk : k=ι 0
      · subst k; simp [Function.iterate_succ_apply]
      · by_cases hkc : k=counter
        · subst k; simp [(hc 0).symm]
        · simp [s₂,s₁,Function.update_of_ne,hk,hkc]
    rw [he] at hi
    have hh := Block.loop_runs_step counter ((Block.pop counter).seq (p.block.rename ι))
      (by simp [hcount]) (Block.seq_runs _ _ hp hp₀) hi
    refine ⟨_,?_,hh⟩
    have ht' : t≤p.time.eval B := ht.trans (polynomial_eval_mono p.time (by simpa using hb 0 (by omega)))
    nlinarith

noncomputable def boundedIterate {δ : Type} (p : Routine ea ea f)
    (count : δ → ℕ) (initial : δ → α) (P : Polynomial ℕ)
    (hbound : ∀ d j,j≤count d → (ea (f^[j] (initial d))).length≤
      P.eval (pairBits (unary (count d)) (ea (initial d))).length) :
    Routine (fun d => pairBits (unary (count d)) (ea (initial d))) ea
      (fun d => f^[count d] (initial d)) where
  scratch := p.scratch+1
  block :=
    let ι : Fin (p.scratch+1) → Fin (p.scratch+2) := fun i => ⟨i.val,by omega⟩
    let c : Fin (p.scratch+2) := ⟨p.scratch+1,by omega⟩
    (Block.decodeRev 0 c).seq (Block.loop c ((Block.pop c).seq (p.block.rename ι)))
  time := X*(p.time.comp P+7)+3
  correct d := by
    let R := p.scratch+2
    let ι : Fin (p.scratch+1) → Fin R := fun i => ⟨i.val,by omega⟩
    let c : Fin R := ⟨p.scratch+1,by omega⟩
    have hι : Function.Injective ι := fun i j h => Fin.ext (congrArg (fun k : Fin R => k.val) h)
    have hc : ∀ i,ι i≠c := by
      intro i h
      have hh := congrArg (fun k : Fin R => k.val) h
      have hi := i.isLt
      simp only [ι,c] at hh
      omega
    have h0c : (0:Fin R)≠c := hc 0
    let e := pairBits (unary (count d)) (ea (initial d))
    let s₀ : Store R := Function.update (fun _ => []) 0 e
    let s₁ : Store R := Function.update (Function.update s₀ 0 (ea (initial d))) c (unary (count d))
    have hd : (Block.decodeRev 0 c).Runs s₀ s₁ (5*count d+2) := by
      simpa [s₁,s₀,h0c.symm] using Block.decodeRev_runs (0:Fin R) c h0c
        (unary (count d)) (ea (initial d)) s₀ (by simp [s₀,e])
    obtain ⟨t,ht,hi⟩ := p.iterate_runs_at ι hι c hc (P.eval e.length) (count d) (initial d) s₁
      (by change s₁ 0=_; simp [s₁,h0c]) (by
        intro i hi
        have hne : ι i≠0 := fun h => hi (hι h)
        simp [s₁,s₀,Function.update_of_ne,hne,hc])
      (by simp [s₁]) (hbound d)
    have he : Function.update (Function.update s₁ c []) (ι 0) (ea (f^[count d] (initial d)))=
        Function.update (fun _ => []) 0 (ea (f^[count d] (initial d))) := by
      funext k
      change Function.update (Function.update s₁ c []) 0 _ k=_
      by_cases hk : k=0
      · subst k; simp
      · by_cases hkc : k=c
        · subst k; simp [h0c.symm]
        · simp [s₁,s₀,Function.update_of_ne,hk,hkc]
    rw [he] at hi
    refine ⟨_,?_,Block.seq_runs _ _ hd hi⟩
    simp only [eval_add,eval_mul,eval_X,eval_comp,eval_ofNat]
    change 5*count d+2+t≤e.length*(p.time.eval (P.eval e.length)+7)+3
    have hn : count d≤e.length := by simp [e,pairBits_length]; omega
    have hmul := Nat.mul_le_mul_right (p.time.eval (P.eval e.length)+7) hn
    nlinarith

end Routine
end BinaryMatching.StackCode
end

end OAI
