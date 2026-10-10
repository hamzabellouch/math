import OAI.Computability.MatchingCount.StackFrame

namespace OAI

section

namespace BinaryMatching.StackCode
open Polynomial

namespace PairRegisters

def left (p q : ℕ) (i : Fin (p+1)) : Fin (p+q+3) := ⟨i.val,by have := i.isLt; omega⟩
def right (p q : ℕ) (i : Fin (q+1)) : Fin (p+q+3) := ⟨p+1+i.val,by have := i.isLt; omega⟩
def aux (p q : ℕ) : Fin (p+q+3) := ⟨p+q+2,by omega⟩

@[simp] lemma left_zero (p q : ℕ) : left p q 0=0 := rfl
lemma left_inj (p q : ℕ) : Function.Injective (left p q) := by
  intro i j h
  exact Fin.ext (congrArg (fun k : Fin (p+q+3) => k.val) h)
lemma right_inj (p q : ℕ) : Function.Injective (right p q) := by
  intro i j h
  have hh := congrArg (fun k : Fin (p+q+3) => k.val) h
  simp only [right] at hh
  exact Fin.ext (by omega)
@[simp] lemma left_ne_right (p q : ℕ) (i : Fin (p+1)) (j : Fin (q+1)) : left p q i≠right p q j := by
  intro h
  have hh := congrArg (fun k : Fin (p+q+3) => k.val) h
  simp only [left,right] at hh
  have := i.isLt
  omega
@[simp] lemma left_ne_aux (p q : ℕ) (i : Fin (p+1)) : left p q i≠aux p q := by
  intro h
  have hh := congrArg (fun k : Fin (p+q+3) => k.val) h
  simp only [left,aux] at hh
  have := i.isLt
  omega
@[simp] lemma right_ne_aux (p q : ℕ) (i : Fin (q+1)) : right p q i≠aux p q := by
  intro h
  have hh := congrArg (fun k : Fin (p+q+3) => k.val) h
  simp only [right,aux] at hh
  have := i.isLt
  omega
@[simp] lemma zero_ne_right (p q : ℕ) (j : Fin (q+1)) : (0:Fin (p+q+3))≠right p q j :=
  left_ne_right p q 0 j
@[simp] lemma zero_ne_aux (p q : ℕ) : (0:Fin (p+q+3))≠aux p q := left_ne_aux p q 0

end PairRegisters

namespace Routine
variable {α β γ : Type} {ea : α → List Bool} {eb : β → List Bool}
  {ec : γ → List Bool} {f : α → β} {g : α → γ}

noncomputable def pair (p : Routine ea eb f) (q : Routine ea ec g) :
    Routine ea (fun z : β×γ => pairBits (eb z.1) (ec z.2)) (fun a => (f a,g a)) where
  scratch := p.scratch+q.scratch+2
  block :=
    let fst := (0:Fin (p.scratch+q.scratch+3))
    let snd := PairRegisters.right p.scratch q.scratch 0
    let aux := PairRegisters.aux p.scratch q.scratch
    (Block.copy fst snd aux).seq
      ((p.block.rename (PairRegisters.left p.scratch q.scratch)).seq
        ((q.block.rename (PairRegisters.right p.scratch q.scratch)).seq
          ((Block.pairInto fst snd aux).seq (Block.moveInto snd fst aux))))
  time := 100*(X+p.time+q.time+1)
  correct a := by
    let R := p.scratch+q.scratch+3
    let d := PairRegisters.right p.scratch q.scratch 0
    let aux := PairRegisters.aux p.scratch q.scratch
    have h0d : (0:Fin R)≠d := PairRegisters.zero_ne_right _ _ _
    have h0a : (0:Fin R)≠aux := PairRegisters.zero_ne_aux _ _
    have hda : d≠aux := PairRegisters.right_ne_aux _ _ _
    let s₀ : Store R := Function.update (fun _ => []) 0 (ea a)
    let s₁ := Function.update s₀ d (ea a)
    let s₂ := Function.update s₁ 0 (eb (f a))
    let s₃ := Function.update s₂ d (ec (g a))
    let s₄ := Function.update (Function.update s₃ 0 []) d (pairBits (eb (f a)) (ec (g a)))
    have hc : (Block.copy 0 d aux).Runs s₀ s₁ (9*(ea a).length+3) := by
      simpa [s₀,s₁,h0d.symm] using Block.copy_runs 0 d aux h0d h0a hda s₀
        (by simp [s₀,h0a.symm])
    obtain ⟨t,ht,hp⟩ := p.run_at (PairRegisters.left p.scratch q.scratch)
      (PairRegisters.left_inj _ _) s₁ a (by simp [s₁,s₀,h0d]) (by
        intro i hi
        have hne : PairRegisters.left p.scratch q.scratch i≠0 := by
          simpa only [←PairRegisters.left_zero p.scratch q.scratch] using
            (fun h => hi (PairRegisters.left_inj _ _ h))
        simp [s₁,s₀,d,PairRegisters.left_ne_right,hne])
    obtain ⟨u,hu,hq⟩ := q.run_at (PairRegisters.right p.scratch q.scratch)
      (PairRegisters.right_inj _ _) s₂ a (by
        change s₂ d=ea a
        simp [s₂,s₁,h0d.symm]) (by
        intro i hi
        have hne : PairRegisters.right p.scratch q.scratch i≠d :=
          fun h => hi (PairRegisters.right_inj _ _ h)
        have hn0 : PairRegisters.right p.scratch q.scratch i≠0 :=
          (PairRegisters.zero_ne_right _ _ _).symm
        simp [s₂,s₁,s₀,Function.update_of_ne,hne,hn0])
    change (p.block.rename (PairRegisters.left _ _)).Runs s₁ s₂ t at hp
    change (q.block.rename (PairRegisters.right _ _)).Runs s₂ s₃ u at hq
    have h₃ : (Block.pairInto 0 d aux).Runs s₃ s₄ (9*(eb (f a)).length+3) := by
      simpa [s₄,s₃,s₂,h0d] using Block.pairInto_runs 0 d aux h0d h0a hda s₃
        (by simp [s₃,s₂,s₁,s₀,h0a.symm,hda.symm])
    have h₄ := Block.moveInto_runs d 0 aux h0d.symm hda h0a s₄
      (by simp [s₄,h0d]) (by simp [s₄,s₃,s₂,s₁,s₀,h0a.symm,hda.symm])
    have hf : Function.update (Function.update s₄ d []) 0 (s₄ d)=
        Function.update (fun _ => []) 0 (pairBits (eb (f a)) (ec (g a))) := by
      funext k
      by_cases hk : k=0
      · subst k; simp [s₄]
      · by_cases hkd : k=d
        · subst k; simp [h0d.symm]
        · simp [s₄,s₃,s₂,s₁,s₀,Function.update_of_ne,hk,hkd]
    rw [hf] at h₄
    have hlen : (s₄ d).length=(pairBits (eb (f a)) (ec (g a))).length := by simp [s₄]
    rw [hlen] at h₄
    have hrun := Block.seq_runs _ _ hc (Block.seq_runs _ _ hp
      (Block.seq_runs _ _ hq (Block.seq_runs _ _ h₃ h₄)))
    refine ⟨_,?_,hrun⟩
    simp only [Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_add,
      Polynomial.eval_X,Polynomial.eval_one,pairBits_length]
    have hf := p.length_bound a
    have hg := q.length_bound a
    omega

end Routine
end BinaryMatching.StackCode
end

end OAI
