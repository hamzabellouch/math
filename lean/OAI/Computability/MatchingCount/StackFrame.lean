import OAI.Computability.MatchingCount.StackPair

namespace OAI

section

namespace BinaryMatching.StackCode

lemma lift_clean {r R : ℕ} (f : Fin (r+1) → Fin R) (hf : Function.Injective f)
    (s : Store R) (hs : ∀ i : Fin (r+1), i≠0 → s (f i)=[]) (v : List Bool) :
    liftStore f (Function.update (fun _ => []) 0 v) s=Function.update s (f 0) v := by
  classical
  funext k
  by_cases hk : ∃ i,f i=k
  · obtain ⟨i,rfl⟩ := hk
    rw [liftStore_at f hf]
    by_cases hi : i=0
    · subst i; simp
    · rw [Function.update_of_ne hi,Function.update_of_ne (fun h => hi (hf h)),hs i hi]
  · rw [liftStore_outside f _ _ k (by simpa only [not_exists] using hk),
      Function.update_of_ne (fun h => hk ⟨0,h.symm⟩)]

namespace Routine
variable {α β : Type} {ea : α → List Bool} {eb : β → List Bool} {f : α → β}

lemma run_at (p : Routine ea eb f) {R : ℕ} (ι : Fin (p.scratch+1) → Fin R)
    (hι : Function.Injective ι) (s : Store R) (a : α)
    (hinput : s (ι 0)=ea a) (hclean : ∀ i, i≠0 → s (ι i)=[]) :
    ∃ t ≤ p.time.eval (ea a).length,
      (p.block.rename ι).Runs s (Function.update s (ι 0) (eb (f a))) t := by
  obtain ⟨t,ht,h⟩ := p.correct a
  have hh := p.block.rename_runs ι hι s h
  rw [lift_clean ι hι s hclean,lift_clean ι hι s hclean,
    ←hinput,Function.update_eq_self] at hh
  exact ⟨t,ht,hh⟩

noncomputable def reindex {α' β' : Type} (p : Routine ea eb f) (ea' : α' → List Bool)
    (eb' : β' → List Bool) (f' : α' → β') (u : α' → α)
    (hin : ∀ a,ea (u a)=ea' a) (hout : ∀ a,eb (f (u a))=eb' (f' a)) :
    Routine ea' eb' f' where
  scratch := p.scratch
  block := p.block
  time := p.time
  correct a := by simpa only [hin,hout] using p.correct (u a)

noncomputable def identity (ea : α → List Bool) : Routine ea ea id where
  scratch := 0
  block := Block.skip
  time := 1
  correct a := ⟨1,by simp,Block.skip_runs _⟩

end Routine
end BinaryMatching.StackCode
end

end OAI
