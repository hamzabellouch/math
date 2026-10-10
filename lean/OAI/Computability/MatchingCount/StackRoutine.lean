import OAI.Computability.MatchingCount.StackEmbed

namespace OAI

section

namespace BinaryMatching.StackCode
open Finset Polynomial

lemma polynomial_eval_mono (p : Polynomial ℕ) : Monotone p.eval := by
  intro a b hab
  simp only [Polynomial.eval_eq_sum]
  apply Finset.sum_le_sum
  intro i hi
  exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hab i)

def volume {r : ℕ} (s : Store r) : ℕ := ∑ i,(s i).length

lemma volume_update {r : ℕ} (s : Store r) (k : Fin r) (v : List Bool) :
    volume (Function.update s k v)+(s k).length=volume s+v.length := by
  classical
  simp only [volume]
  rw [←Finset.sum_erase_add _ _ (Finset.mem_univ k),
    ←Finset.sum_erase_add (Finset.univ) (fun i => (s i).length) (Finset.mem_univ k)]
  simp only [Function.update_self]
  have he : ∑ i∈Finset.univ.erase k,(Function.update s k v i).length =
      ∑ i∈Finset.univ.erase k,(s i).length := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hi)]
  rw [he]
  omega

lemma volume_instruction {r : ℕ} {L : Type} (i : Instr r L) (s : Store r) :
    volume (i.eval s).2≤volume s+1 := by
  cases i with
  | go q => exact Nat.le_succ _
  | push k b q =>
    have h := volume_update s k (b::s k)
    simp only [Instr.eval,List.length_cons] at *
    omega
  | pop k q =>
    have h := volume_update s k (s k).tail
    have hh : (s k).tail.length≤(s k).length := by simp
    simp only [Instr.eval] at *
    omega
  | branch k e z o => exact Nat.le_succ _

lemma Steps.volume_bound {r : ℕ} {L : Type} {code : L → Instr r (Option L)}
    {q s q' s' t} (h : Steps code q s q' s' t) : volume s'≤volume s+t := by
  induction h with
  | refl => exact le_rfl
  | next q s q' s' t h ih =>
    have he := volume_instruction (code q) s
    omega

lemma volume_single {r : ℕ} (k : Fin r) (s : List Bool) :
    volume (Function.update (fun _ => []) k s)=s.length := by
  classical
  unfold volume
  rw [Finset.sum_eq_single k]
  · simp
  · intro i hi hik
    simp [Function.update_of_ne hik]
  · simp

structure Routine {α β : Type} (ea : α → List Bool) (eb : β → List Bool) (f : α → β) where
  scratch : ℕ
  block : Block (scratch+1)
  time : Polynomial ℕ
  correct : ∀ a, ∃ t≤time.eval (ea a).length,
    block.Runs (Function.update (fun _ => []) 0 (ea a))
      (Function.update (fun _ => []) 0 (eb (f a))) t

namespace Routine
variable {α β γ : Type} {ea : α → List Bool} {eb : β → List Bool}
  {ec : γ → List Bool} {f : α → β} {g : β → γ}

lemma length_bound (p : Routine ea eb f) (a : α) :
    (eb (f a)).length≤(ea a).length+p.time.eval (ea a).length := by
  obtain ⟨t,ht,h⟩ := p.correct a
  have hv := h.volume_bound
  simp only [volume_single] at hv
  omega

private def embedding (r s : ℕ) : Fin (r+1) → Fin (r+s+1) :=
  Fin.castLE (by omega)

private lemma embedding_injective (r s : ℕ) : Function.Injective (embedding r s) := by
  intro a b h
  exact Fin.ext (congrArg (fun x : Fin (r+s+1) => x.val) h)

private lemma embedding_zero (r s : ℕ) : embedding r s 0=0 := rfl

lemma lift_initial {r R : ℕ} (hR : 0<R) (f : Fin (r+1) → Fin R) (hf : Function.Injective f)
    (hz : f 0=⟨0,hR⟩) (v : List Bool) :
    liftStore f (Function.update (fun _ => []) 0 v) (fun _ => [])=
      Function.update (fun _ => []) ⟨0,hR⟩ v := by
  rw [liftStore_update f hf,hz]
  congr 1
  exact liftStore_eq f _ _ (fun _ => rfl)

noncomputable def comp (p : Routine ea eb f) (q : Routine eb ec g) : Routine ea ec (g ∘ f) where
  scratch := p.scratch+q.scratch
  block := (p.block.rename (embedding p.scratch q.scratch)).seq
    (q.block.rename (fun i => ⟨i.val,by have := i.isLt; omega⟩))
  time := p.time+q.time.comp (X+p.time)
  correct a := by
    obtain ⟨t,ht,hp⟩ := p.correct a
    obtain ⟨u,hu,hq⟩ := q.correct (f a)
    let f₁ := embedding p.scratch q.scratch
    let f₂ : Fin (q.scratch+1) → Fin (p.scratch+q.scratch+1) :=
      fun i => ⟨i.val,by have := i.isLt; omega⟩
    have hf₁ : Function.Injective f₁ := embedding_injective _ _
    have hf₂ : Function.Injective f₂ := by
      intro i j h
      exact Fin.ext (congrArg (fun x : Fin (p.scratch+q.scratch+1) => x.val) h)
    have hm₁ := p.block.rename_runs f₁ hf₁ (fun _ => []) hp
    have hm₂ := q.block.rename_runs f₂ hf₂ (fun _ => []) hq
    rw [lift_initial (by omega) f₁ hf₁ rfl,lift_initial (by omega) f₁ hf₁ rfl] at hm₁
    rw [lift_initial (by omega) f₂ hf₂ rfl,lift_initial (by omega) f₂ hf₂ rfl] at hm₂
    refine ⟨t+u,?_,Block.seq_runs _ _ hm₁ hm₂⟩
    simp only [Polynomial.eval_add,Polynomial.eval_comp,Polynomial.eval_X]
    exact Nat.add_le_add ht (hu.trans (polynomial_eval_mono q.time (p.length_bound a)))

noncomputable def machine (p : Routine ea eb f) : Turing.TM2ComputableInPolyTime ea eb f where
  tm := p.block.machine 0 0
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := p.time
  outputsFun a := by
    let t := (p.correct a).choose
    have ht := (p.correct a).choose_spec.1
    have h := (p.correct a).choose_spec.2
    have hm := p.block.machine_runs 0 0 (ea a) (eb (f a)) h
    change Turing.TM2OutputsInTime (p.block.machine 0 0) (List.map id (ea a))
      (some (List.map id (eb (f a)))) (p.time.eval (ea a).length)
    rw [List.map_id_fun,List.map_id_fun]
    exact ⟨hm.toEvalsTo,hm.steps_le_m.trans ht⟩

lemma machine_alphabets_finite (p : Routine ea eb f) (k : p.machine.tm.K) :
    Finite (p.machine.tm.Γ k) := by
  change Finite Bool
  infer_instance

end Routine
end BinaryMatching.StackCode
end

end OAI
