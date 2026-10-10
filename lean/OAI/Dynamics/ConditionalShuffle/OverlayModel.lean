import OAI.Dynamics.ConditionalShuffle.Main

namespace OAI

noncomputable section
open scoped Classical
namespace Revealed.Overlay
open Thorp Thorp.Conditional Split

variable {ι α : Type} [fintype_ι : Fintype ι] [fintype_α : Fintype α] [decidableEq_α : DecidableEq α]

def isActive (D s : ℕ) : Bool := decide (s % (21 * D) ≥ 20 * D)

def xorCoins (d : ℕ) (L : Sum ι α ≃ Position (d+1)) (active : Bool)
    (c r : Coins (d+1)) : Coins (d+1) := fun x =>
  c x ^^ (if active && freePairMask d (avoid (fun i => L (.inl i))) x then r x else false)

lemma xorCoins_occupied (d : ℕ) (L : Sum ι α ≃ Position (d+1)) (active : Bool)
    (c r : Coins (d+1)) (i : ι) :
    step (d+1) (xorCoins d L active c r) (L (.inl i)) = step (d+1) c (L (.inl i)) := by
  let retained_fintype_ι := fintype_ι
  let retained_fintype_α := fintype_α
  let retained_decidableEq_α := decidableEq_α
  have hf : avoid (fun j => L (.inl j)) (L (.inl i)) = false := by
    simp [avoid]
  obtain ⟨⟨b,x⟩, hx⟩ := (splitPosition d).symm.surjective (L (.inl i))
  change Fin.cons b x = L (.inl i) at hx
  rw [← hx] at hf ⊢
  calc
    _ = scatterPosition d (b ^^ xorCoins d L active c r x, x) := step_cons d _ b x
    _ = scatterPosition d (b ^^ c x, x) := by
      cases b <;> simp [xorCoins, freePairMask, hf]
    _ = _ := (step_cons d c b x).symm

def multiplier (d : ℕ) (L : Sum ι α ≃ Position (d+1)) (active : Bool)
    (c r : Coins (d+1)) : Equiv.Perm α :=
  relative (L.trans (step (d+1) c)) (L.trans (step (d+1) (xorCoins d L active c r)))
    (fun i => (xorCoins_occupied d L active c r i).symm)

def overlayRun (d : ℕ) (L : Sum ι α ≃ Position (d+1)) (schedule : ℕ → Bool) :
    (t : ℕ) → History (d+1) t → History (d+1) t → Equiv.Perm α
  | 0, _, _ => 1
  | t+1, c, r =>
      multiplier d (L.trans (run (d+1) t (Fin.init c))) (schedule t)
        (c (Fin.last t)) (r (Fin.last t)) *
      overlayRun d L schedule t (Fin.init c) (Fin.init r)

def conditionalLaw (d : ℕ) (L : Sum ι α ≃ Position (d+1)) (schedule : ℕ → Bool)
    (t : ℕ) (c : History (d+1) t) : Equiv.Perm α → ℝ :=
  fairMass (overlayRun d L schedule t c)

def expectedTV (d : ℕ) (L : Sum ι α ≃ Position (d+1)) (schedule : ℕ → Bool)
    (t : ℕ) : ℝ := mean (fun c : History (d+1) t =>
      tv (conditionalLaw d L schedule t c)
        (fun _ => (Fintype.card (Equiv.Perm α) : ℝ)⁻¹))

abbrev OutsideLabels (d : ℕ) := Fin 7 × Position d

def standardLayout (d : ℕ) : Sum (OutsideLabels d) (Position d) ≃ Position (d+3) :=
  Fintype.equivOfCardEq (by simp [OutsideLabels, Position, pow_add]; omega)

def worstCallTV (d : ℕ) : ℝ :=
  (Finset.univ : Finset (State (d+3))).sup' ⟨1, Finset.mem_univ _⟩ (fun g₀ : State (d+3) =>
    expectedTV (d+2) ((standardLayout d).trans g₀) (isActive (d+3))
      (65536 * 21 * (d+3)))

end Revealed.Overlay

end

end OAI
