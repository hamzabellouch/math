import Mathlib

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped ContDiff

namespace StrictHotSpots

abbrev Plane := EuclideanSpace ℝ (Fin 2)

def SmoothBoundary (Ω : Set Plane) : Prop :=
  ∀ p ∈ frontier Ω, ∃ (U : Set Plane) (ρ : Plane → ℝ),
    IsOpen U ∧ p ∈ U ∧ ContDiffOn ℝ ∞ ρ U ∧
    fderiv ℝ ρ p ≠ 0 ∧ ρ p = 0 ∧
    Ω ∩ U = {x | ρ x < 0} ∩ U

def AdmissibleDomain (Ω : Set Plane) : Prop :=
  Ω.Nonempty ∧ IsOpen Ω ∧ Bornology.IsBounded Ω ∧
    IsSimplyConnected Ω ∧ SmoothBoundary Ω

def HasH1Gradient (Ω : Set Plane) (v : Plane → ℝ) (g : Plane → Plane) : Prop :=
  MemLp v 2 (volume.restrict Ω) ∧ MemLp g 2 (volume.restrict Ω) ∧
  ∀ φ : Plane → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ Ω →
    ∀ e : Plane,
      (∫ x in Ω, v x * (fderiv ℝ φ x) e) =
        -(∫ x in Ω, (inner ℝ (g x) e) * φ x)

def rayleighValues (Ω : Set Plane) : Set ℝ :=
  {r | ∃ (v : Plane → ℝ) (g : Plane → Plane),
    HasH1Gradient Ω v g ∧ (∫ x in Ω, v x) = 0 ∧
    0 < (∫ x in Ω, (v x) ^ 2) ∧
    r = (∫ x in Ω, ‖g x‖ ^ 2) / (∫ x in Ω, (v x) ^ 2)}

def firstPositiveNeumannValue (Ω : Set Plane) : ℝ := sInf (rayleighValues Ω)

def InFirstNeumannEigenspace (Ω : Set Plane) (u : Plane → ℝ) : Prop :=
  ContDiffOn ℝ ∞ u (closure Ω) ∧ HasH1Gradient Ω u (gradient u) ∧
    (∫ x in Ω, u x) = 0 ∧
    ∀ (v : Plane → ℝ) (g : Plane → Plane), HasH1Gradient Ω v g →
      (∫ x in Ω, inner ℝ (gradient u x) (g x)) =
        firstPositiveNeumannValue Ω * (∫ x in Ω, u x * v x)

def MainConclusion (Ω : Set Plane) (u : Plane → ℝ) : Prop :=
  (∀ x ∈ Ω, gradient u x ≠ 0) ∧
    ∀ x ∈ Ω, sInf (u '' frontier Ω) < u x ∧ u x < sSup (u '' frontier Ω)

theorem main_theorem (Ω : Set Plane) (hΩ : AdmissibleDomain Ω)
    (u : Plane → ℝ) (hu : InFirstNeumannEigenspace Ω u)
    (hne : ∃ x ∈ Ω, u x ≠ 0) : MainConclusion Ω u := by
  sorry

end StrictHotSpots
end

end OAI
