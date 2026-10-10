import OAI.Computability.PerfectCompleteness.Foundations.WholeCutReplayKeys

namespace OAI

section

namespace PerfectCompleteness.CutSlotAssembly

noncomputable section

open scoped Classical
open RecursiveSpaces DescendantSpaces TreeSourceSpaces

variable {branch : Nat → Nat} {n m : Nat} {V : Type*}

def fill : {n m : Nat} → Path branch n m →
    (Slots branch n → V) → (Slots branch m → V) → Slots branch n → V
  | _, _, .refl _, _, inside, s => inside s
  | _, _, .step i p, outside, inside, s =>
      if s.1 = i then fill p (fun j => outside (i, j)) inside s.2 else outside s

@[simp] theorem fill_at_cut (p : Path branch n m)
    (outside : Slots branch n → V) (inside : Slots branch m → V)
    (s : Slots branch m) :
    fill p outside inside (p.slotEmbedding s) = inside s := by
  revert outside inside s
  induction p with
  | refl _ => intros; rfl
  | step i p ih =>
      intro outside inside s
      simp only [fill, Path.slotEmbedding]
      exact ih (fun j => outside (i, j)) inside s

theorem fill_restrict (p : Path branch n m) (outside : Slots branch n → V) :
    fill p outside (fun s => outside (p.slotEmbedding s)) = outside := by
  induction p with
  | refl _ => rfl
  | step i p ih =>
      funext s
      by_cases hs : s.1 = i
      · obtain ⟨j, s⟩ := s
        dsimp only at hs
        subst j
        simp only [fill]
        exact congrFun (ih (fun j => outside (i, j))) s
      · simp only [fill, ite_eq_right hs]

theorem fill_kept_eq (p : Path branch n (m + 1))
    (outside : Slots branch n → V) (left right : Slots branch (m + 1) → V)
    (clean : Fin (branch m) → Prop)
    (h : ∀ (i : Fin (branch m)), ¬ clean i → ∀ s, left (i, s) = right (i, s)) :
    ∀ s, CutSamplerKeyLocality.keptLeaf p clean s →
      fill p outside left s = fill p outside right s := by
  revert outside left right clean h
  induction n generalizing m with
  | zero =>
      have hp := p.height_le
      omega
  | succ n ih =>
      cases p with
      | refl =>
          intro outside left right clean h s hs
          exact h s.1 hs s.2
      | step i p =>
          intro outside left right clean h s hs
          by_cases hi : s.1 = i
          · simp only [fill, ite_eq_left hi]
            exact ih p (fun j => outside (i, j)) left right clean h s.2
              (hs.resolve_left (not_not_intro hi))
          · simp only [fill, ite_eq_right hi]

section Replay

variable {t : Nat} (rows repeats : Nat → Nat)
  (p : Path branch n (m + 1))
  (outside : Slots branch n → Fin t → MixedSupport.Slot)
  (reference target : Slots branch (m + 1) → Fin t → MixedSupport.Slot)
  (clean : Fin (branch m) → Prop)
  (h : ∀ (i : Fin (branch m)), ¬ clean i → ∀ s, reference (i, s) = target (i, s))

def transport (tape : WholeCutReplay.Tape rows repeats p (fill p outside reference) clean) :
    WholeCutReplay.Tape rows repeats p (fill p outside target) clean :=
  WholeCutReplayKeys.transportTape rows repeats p (fill p outside reference)
    (fill p outside target) clean (fill_kept_eq p outside reference target clean h) tape

end Replay

end
end PerfectCompleteness.CutSlotAssembly

end

end OAI
