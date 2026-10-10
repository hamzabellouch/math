import OAI.NumberTheory.Ostmann.Construction.InitialCoordinatesTemplateState

namespace OAI

noncomputable section
namespace Ostmann.Construction.InitialCoordinatesTemplate
open Arithmetic
variable {b s k : ℕ} {a : State} {outside : List ℕ}

def topCenters (b : ℕ) (center : ℕ → ℝ) (h : Bool) (i : Fin 3) : ℝ :=
  center (2*b+(if h then 3 else 0)+i.val)

def compensationCenters (b : ℕ) (center : ℕ → ℝ) (h : Bool) (j : Fin k) (i : Fin 2) : ℝ :=
  center (2*b+6+4*j.val+(if h then 2 else 0)+i.val)

theorem coordinates_top_cells
    (ha : Template.Matches (Template.initial (2*b) k) a.small)
    (hout : outside.length = 2*s) (plus minus : ℝ)
    (y : Fin a.small.length → ℝ) (z : Fin outside.length → ℝ) (center : ℕ → ℝ)
    (hcell : ∀i, (a.small.get i).role ≠ .bulk →
      |Real.log (y i) - center (a.small.get i).origin| ≤ 1) :
    ∀h i, |Real.log ((coordinates ha hout plus minus y z).top h i) - topCenters b center h i| ≤ 1 := by
  intro h i
  let q := stateIndex ha (.inr (.inl (h,i)))
  obtain ⟨ho,hr⟩ := matches_initial_metadata ha q
  have hn : (a.small.get q).role ≠ .bulk := by
    intro he
    have hi := hr.mp he
    dsimp [q] at hi
    rw [smallEquiv_top_val] at hi
    omega
  have hc := hcell q hn
  rw [ho] at hc
  simpa only [q, stateIndex_val, smallEquiv_top_val, coordinates, topCenters] using hc

theorem coordinates_compensation_cells
    (ha : Template.Matches (Template.initial (2*b) k) a.small)
    (hout : outside.length = 2*s) (plus minus : ℝ)
    (y : Fin a.small.length → ℝ) (z : Fin outside.length → ℝ) (center : ℕ → ℝ)
    (hcell : ∀i, (a.small.get i).role ≠ .bulk →
      |Real.log (y i) - center (a.small.get i).origin| ≤ 1) :
    ∀h j i, |Real.log ((coordinates ha hout plus minus y z).compensation h j i) -
      compensationCenters b center h j i| ≤ 1 := by
  intro h j i
  let q := stateIndex ha (.inr (.inr (j,(h,i))))
  obtain ⟨ho,hr⟩ := matches_initial_metadata ha q
  have hn : (a.small.get q).role ≠ .bulk := by
    intro he
    have hi := hr.mp he
    dsimp [q] at hi
    rw [smallEquiv_compensation_val] at hi
    omega
  have hc := hcell q hn
  rw [ho] at hc
  simpa only [q, stateIndex_val, smallEquiv_compensation_val, coordinates, compensationCenters] using hc

end Ostmann.Construction.InitialCoordinatesTemplate

end

end OAI
