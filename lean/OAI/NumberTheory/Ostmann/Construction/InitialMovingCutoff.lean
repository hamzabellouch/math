import OAI.NumberTheory.Ostmann.Construction.InitialMovingCoefficient
import OAI.NumberTheory.Ostmann.Construction.InitialCutoffProduct

namespace OAI

/-! # The original logarithmic cutoffs depend only on retained bulk data -/
namespace Ostmann
open scoped Classical BigOperators

theorem initialHalfAssemble_bulk {P : Type*} (b d r : ℕ)
    (sl : Fin d → P) (y : InitialRetainedSlot b r → P) (i : Fin b) :
    initialHalfAssemble b d r sl y (i.castAdd (d + r)).succ = y (.inr (.inl i)) := by
  change (Sum.elim sl y) ((initialSpectatorSlotEquiv b d r).symm
    (initialSpectatorSlotEquiv b d r (.inr (.inr (.inl i))))) = _
  rw [Equiv.symm_apply_apply]
  rfl

theorem initialHalfCutoffWeight_assembled {P : Type*} (value : P → ℕ) (b d r : ℕ)
    (cb cd : ℝ) (sl : Fin d → P) (y : InitialRetainedSlot b r → P) :
    initialHalfCutoffWeight value b d r cb cd (Fin.tail (initialHalfAssemble b d r sl y)) =
      initialLogSumWeight value cb (fun i => y (.inr (.inl i))) *
        initialLogSumWeight value cd sl := by
  unfold initialHalfCutoffWeight
  simp only [Fin.tail, initialHalfAssemble_bulk, initialHalfAssemble_spectator]

noncomputable def initialMovingCutoffWeight {P : Type*} (value : P → ℕ) (b d r : ℕ)
    (cb cd : ℝ) (sl sr : Fin d → P) (y : MovingRegularSlot 0 (r + r) (b + b) → P) : ℂ :=
  ((initialLogSumWeight value cb (fun i : Fin b => y ((), .inr (i.castAdd b))) *
    initialLogSumWeight value cd sl : ℝ) : ℂ) *
  ((initialLogSumWeight value cb (fun i : Fin b => y ((), .inr (Fin.natAdd b i))) *
    initialLogSumWeight value cd sr : ℝ) : ℂ)

theorem initialMovingTuple_cutoff {P : Type*} (value : P → ℕ) (b d r : ℕ)
    (cb cd : ℝ) (sl sr : Fin d → P) (XL XR : P)
    (y : MovingRegularSlot 0 (r + r) (b + b) → P) :
    doubledHalfWeight (fun x : Fin (b + (d + r) + 1) → P =>
      (initialHalfCutoffWeight value b d r cb cd (Fin.tail x) : ℂ))
      (initialMovingTuple b d r sl sr XL XR y) =
    initialMovingCutoffWeight value b d r cb cd sl sr y := by
  let z : Bool ⊕ MovingRegularSlot 0 (r + r) (b + b) → P :=
    Sum.elim (fun a : Bool => if a then XL else XR) y
  have hx := initial_reassembled_moving_tuple b d r sl sr z
  change _ = initialMovingTuple b d r sl sr XL XR y at hx
  rw [← hx]
  simp only [doubledHalfWeight, Fin.append_left, Fin.append_right]
  change (initialHalfCutoffWeight value b d r cb cd
    (Fin.tail (initialHalfAssemble b d r sl (z ∘ initialRetainedIndexEquiv b r ∘ Sum.inl))) : ℂ) *
      (initialHalfCutoffWeight value b d r cb cd
    (Fin.tail (initialHalfAssemble b d r sr (z ∘ initialRetainedIndexEquiv b r ∘ Sum.inr))) : ℂ) = _
  rw [initialHalfCutoffWeight_assembled, initialHalfCutoffWeight_assembled]
  rfl

end Ostmann

end OAI
