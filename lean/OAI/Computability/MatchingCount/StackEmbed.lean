import OAI.Computability.MatchingCount.StackCopy

namespace OAI

section

namespace BinaryMatching.StackCode

noncomputable def liftStore {r R : ℕ} (f : Fin r → Fin R) (s : Store r) (base : Store R) : Store R :=
  fun k => if h : ∃ i,f i=k then s h.choose else base k

lemma liftStore_at {r R : ℕ} (f : Fin r → Fin R) (hf : Function.Injective f)
    (s : Store r) (base : Store R) (i : Fin r) : liftStore f s base (f i)=s i := by
  classical
  unfold liftStore
  have h : ∃ j,f j=f i := ⟨i,rfl⟩
  rw [dite_eq_left h]
  rw [hf h.choose_spec]

lemma liftStore_outside {r R : ℕ} (f : Fin r → Fin R) (s : Store r) (base : Store R)
    (k : Fin R) (hk : ∀ i,f i≠k) : liftStore f s base k=base k := by
  classical
  exact dite_eq_right (by simpa only [not_exists] using hk)

lemma liftStore_update {r R : ℕ} (f : Fin r → Fin R) (hf : Function.Injective f)
    (s : Store r) (base : Store R) (i : Fin r) (v : List Bool) :
    liftStore f (Function.update s i v) base=Function.update (liftStore f s base) (f i) v := by
  classical
  funext k
  by_cases hk : ∃ j,f j=k
  · obtain ⟨j,rfl⟩ := hk
    rw [liftStore_at f hf]
    by_cases hji : j=i
    · subst j; simp
    · rw [Function.update_of_ne hji,Function.update_of_ne (fun h => hji (hf h)),liftStore_at f hf]
  · have ho : ∀ j,f j≠k := by simpa only [not_exists] using hk
    rw [liftStore_outside f _ base k ho,Function.update_of_ne (ho i).symm,
      liftStore_outside f _ base k ho]

lemma liftStore_eq {r R : ℕ} (f : Fin r → Fin R) (s : Store r) (base : Store R)
    (h : ∀ i,base (f i)=s i) : liftStore f s base=base := by
  classical
  funext k
  unfold liftStore
  split_ifs with hk
  · rw [←h, hk.choose_spec]
  · rfl

namespace Instr
variable {r R : ℕ} {L : Type}

def rename (f : Fin r → Fin R) : Instr r L → Instr R L
  | .go q => .go q
  | .push k b q => .push (f k) b q
  | .pop k q => .pop (f k) q
  | .branch k e z o => .branch (f k) e z o

lemma eval_rename (f : Fin r → Fin R) (hf : Function.Injective f) (i : Instr r L)
    (s : Store r) (base : Store R) :
    (i.rename f).eval (liftStore f s base)=((i.eval s).1,liftStore f (i.eval s).2 base) := by
  cases i with
  | go q => rfl
  | push k b q => simp only [rename,eval,liftStore_at f hf,liftStore_update f hf]
  | pop k q => simp only [rename,eval,liftStore_at f hf,liftStore_update f hf]
  | branch k e z o => simp only [rename,eval,liftStore_at f hf]
end Instr

namespace Steps
variable {r R : ℕ} {L : Type} {code : L → Instr r (Option L)}

lemma rename (f : Fin r → Fin R) (hf : Function.Injective f) (base : Store R)
    {q s q' s' t} (h : Steps code q s q' s' t) :
    Steps (fun l => (code l).rename f) q (liftStore f s base) q' (liftStore f s' base) t := by
  induction h with
  | refl => exact .refl _ _
  | next q s q' s' t h ih =>
    apply Steps.next
    simpa only [Instr.eval_rename f hf] using ih
end Steps

namespace Block
variable {r R : ℕ}

def rename (b : Block r) (f : Fin r → Fin R) : Block R where
  Label := b.Label
  finite := b.finite
  entry := b.entry
  code l := (b.code l).rename f

lemma rename_runs (b : Block r) (f : Fin r → Fin R) (hf : Function.Injective f)
    (base : Store R) {s s' : Store r} {t : ℕ} (h : b.Runs s s' t) :
    (b.rename f).Runs (liftStore f s base) (liftStore f s' base) t := h.rename f hf base

end Block
end BinaryMatching.StackCode
end

end OAI
