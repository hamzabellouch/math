import Mathlib.Data.ZMod.Basic
import OAI.Combinatorics.Progressions.Estimates.ActiveAveragedProfileComparison

namespace OAI

section

namespace Erdos3

open scoped Classical

noncomputable def booleanJetResidueMask {D α : Type*} [DecidableEq α]
    {O : D → Type*} (sets : ∀ d, O d → Finset α) (m : ℕ)
    (mask : ((Σ d, O d) → ZMod m) → ℂ) (r : Finset α → D → ZMod m) : ℂ :=
  mask (fun o => booleanCoefficient (fun s => r s o.1) (sets o.1 o.2))

theorem booleanJetResidueMask_cast {D α : Type*} [DecidableEq α]
    {O : D → Type*} (sets : ∀ d, O d → Finset α) (m : ℕ)
    (mask : ((Σ d, O d) → ZMod m) → ℂ) (z : Finset α → D → ℤ) :
    booleanJetResidueMask sets m mask (fun s d => (z s d : ZMod m)) =
      mask (fun o => (booleanCoefficient (fun s => z s o.1) (sets o.1 o.2) : ℤ)) := by
  unfold booleanJetResidueMask
  congr 1
  funext o
  exact (booleanCoefficient_map (Int.castRingHom (ZMod m)) (fun s => z s o.1) (sets o.1 o.2)).symm

theorem booleanJetResidueMask_bound {D α : Type*} [DecidableEq α]
    {O : D → Type*} (sets : ∀ d, O d → Finset α) (m : ℕ)
    (mask : ((Σ d, O d) → ZMod m) → ℂ) {G : ℝ} (hm : ∀ r, ‖mask r‖ ≤ G)
    (r : Finset α → D → ZMod m) : ‖booleanJetResidueMask sets m mask r‖ ≤ G := hm _

theorem siteResidueVector_card_le_exp (D : Type*) [Fintype D] (m : ℕ) [NeZero m]
    {P : ℝ} (hm : (m : ℝ) ≤ Real.exp P) :
    (Fintype.card (D → ZMod m) : ℝ) ≤ Real.exp (Fintype.card D*P) := by
  simp only [Fintype.card_fun, ZMod.card, Nat.cast_pow]
  calc
    _ ≤ (Real.exp P)^Fintype.card D := by gcongr
    _ = _ := (Real.exp_nat_mul _ _).symm

end Erdos3

end

end OAI
