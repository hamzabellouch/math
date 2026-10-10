import OAI.Dynamics.ConditionalShuffle.ResetMinorization

namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace Revealed.Overlay
open Thorp Thorp.Conditional Revealed.Split Revealed.Disintegration

def maskedXor (d : ℕ) (m : Position d → Bool) (c r : Coins (d+1)) : Coins (d+1) :=
  fun x => c x ^^ (if m x then r x else false)

lemma maskedXor_involutive (d : ℕ) (m : Position d → Bool) (r : Coins (d+1)) :
    Function.Involutive (fun c => maskedXor d m c r) := by
  intro c; funext x
  change ((c x ^^ (if m x then r x else false)) ^^ (if m x then r x else false)) = c x
  simp

def predictableHistory (d : ℕ)
    (M : (t : ℕ) → History (d+1) t → History (d+1) t → Position d → Bool) :
    (t : ℕ) → History (d+1) t → History (d+1) t → History (d+1) t
  | 0, _, _ => Fin.elim0
  | t+1, c, r => Fin.snoc (predictableHistory d M t (Fin.init c) (Fin.init r))
      (maskedXor d (M t (Fin.init c) (Fin.init r)) (c (Fin.last t)) (r (Fin.last t)))

lemma predictableHistory_injective (d : ℕ)
    (M : (t : ℕ) → History (d+1) t → History (d+1) t → Position d → Bool)
    (t : ℕ) (r : History (d+1) t) : Function.Injective (fun c => predictableHistory d M t c r) := by
  induction t with
  | zero => intro c c' _; exact Subsingleton.elim _ _
  | succ t ih =>
      intro c c' h
      have hp := congrArg Fin.init h
      simp only [predictableHistory, Fin.init_snoc] at hp
      have hc := ih (Fin.init r) hp
      have hl := congrFun h (Fin.last t)
      simp only [predictableHistory, Fin.snoc_last, hc] at hl
      have hl' := (maskedXor_involutive d (M t (Fin.init c') (Fin.init r)) (r (Fin.last t))).injective hl
      calc
        c = Fin.snoc (Fin.init c) (c (Fin.last t)) := (Fin.snoc_init_self c).symm
        _ = Fin.snoc (Fin.init c') (c' (Fin.last t)) := by rw [hc, hl']
        _ = c' := Fin.snoc_init_self c'

def predictableEquiv (d : ℕ)
    (M : (t : ℕ) → History (d+1) t → History (d+1) t → Position d → Bool)
    (t : ℕ) (r : History (d+1) t) : Equiv.Perm (History (d+1) t) :=
  Equiv.ofBijective (fun c => predictableHistory d M t c r)
    ((Fintype.bijective_iff_injective_and_card _).mpr
      ⟨predictableHistory_injective d M t r, rfl⟩)

lemma predictable_law (d : ℕ)
    (M : (t : ℕ) → History (d+1) t → History (d+1) t → Position d → Bool)
    (t : ℕ) (r : History (d+1) t) :
    fairMass (fun c : History (d+1) t => run (d+1) t (predictableHistory d M t c r)) = law (d+1) t := by
  exact fairMass_comp_equiv (run (d+1) t) (predictableEquiv d M t r)

variable {ι α : Type} [fintype_ι : Fintype ι] [fintype_α : Fintype α] [decidableEq_α : DecidableEq α]

def modifiedHistory (d : ℕ) (L : Sum ι α ≃ Position (d+1)) (σ : ℕ → Bool)
    (t : ℕ) (c r : History (d+1) t) : History (d+1) t :=
  predictableHistory d (fun k a _ => mask d (L.trans (run (d+1) k a)) (σ k)) t c r

lemma modifiedHistory_succ (d : ℕ) (L : Sum ι α ≃ Position (d+1)) (σ : ℕ → Bool)
    (t : ℕ) (c r : History (d+1) (t+1)) :
    modifiedHistory d L σ (t+1) c r =
      Fin.snoc (modifiedHistory d L σ t (Fin.init c) (Fin.init r))
        (xorCoins d (L.trans (run (d+1) t (Fin.init c))) (σ t) (c (Fin.last t)) (r (Fin.last t))) := by
  let retained_fintype_ι := fintype_ι
  let retained_fintype_α := fintype_α
  let retained_decidableEq_α := decidableEq_α
  exact rfl

theorem overlay_physical_law (d : ℕ) (L : Sum ι α ≃ Position (d+1)) (σ : ℕ → Bool)
    (t : ℕ) (r : History (d+1) t) :
    fairMass (fun c : History (d+1) t => run (d+1) t (modifiedHistory d L σ t c r)) = law (d+1) t := by
  let retained_fintype_ι := fintype_ι
  let retained_fintype_α := fintype_α
  let retained_decidableEq_α := decidableEq_α
  exact predictable_law d _ t r

lemma modified_outside (d : ℕ) (L : Sum ι α ≃ Position (d+1)) (σ : ℕ → Bool)
    (t : ℕ) (c r : History (d+1) t) (i : ι) :
    run (d+1) t (modifiedHistory d L σ t c r) (L (.inl i)) =
      run (d+1) t c (L (.inl i)) := by
  induction t with
  | zero => simp only [run_zero, Equiv.Perm.one_apply]
  | succ t ih =>
      rw [modifiedHistory_succ, run_succ, run_succ]
      simp only [Fin.snoc_last, Fin.snoc_castSucc, Equiv.Perm.mul_apply]
      rw [ih]
      exact xorCoins_occupied d (L.trans (run (d+1) t (Fin.init c))) (σ t) _ _ i

lemma modified_inside (d : ℕ) (L : Sum ι α ≃ Position (d+1)) (σ : ℕ → Bool)
    (t : ℕ) (c r : History (d+1) t) (a : α) :
    run (d+1) t (modifiedHistory d L σ t c r) (L (.inr a)) =
      run (d+1) t c (L (.inr (overlayRun d L σ t c r a))) := by
  induction t with
  | zero => simp only [run_zero, overlayRun, Equiv.Perm.one_apply]
  | succ t ih =>
      rw [modifiedHistory_succ, run_succ, run_succ, overlayRun]
      simp only [Fin.snoc_last, Fin.snoc_castSucc, Equiv.Perm.mul_apply]
      rw [ih]
      exact (multiplier_forward d (L.trans (run (d+1) t (Fin.init c))) (σ t) _ _ _).symm

theorem overlay_incoming_factor (d : ℕ) (L : Sum ι α ≃ Position (d+1)) (σ : ℕ → Bool)
    (t : ℕ) (c r : History (d+1) t) (π : Equiv.Perm α) :
    (Equiv.sumCongr (Equiv.refl ι) π).trans (L.trans (run (d+1) t (modifiedHistory d L σ t c r))) =
      (Equiv.sumCongr (Equiv.refl ι) (overlayRun d L σ t c r * π)).trans (L.trans (run (d+1) t c)) := by
  apply Equiv.ext; intro x
  cases x with
  | inl i => exact modified_outside d L σ t c r i
  | inr a => exact modified_inside d L σ t c r (π a)

end Revealed.Overlay

end

end OAI
