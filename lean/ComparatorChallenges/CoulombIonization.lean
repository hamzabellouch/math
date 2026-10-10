import Mathlib

namespace OAI

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

noncomputable section
namespace CoulombAtom

abbrev Space := EuclideanSpace ℝ (Fin 3)
abbrev Configuration (N : ℕ) := Fin N → Space
abbrev Spins (N : ℕ) := Fin N → Fin 2

structure FormVector (N : ℕ) where
  value : Spins N → Configuration N → ℂ
  gradient : Spins N → Fin N → Fin 3 → Configuration N → ℂ

def direction {N : ℕ} (i : Fin N) (a : Fin 3) : Configuration N :=
  Pi.single i (EuclideanSpace.single a 1)

def FormAdmissible {N : ℕ} (ψ : FormVector N) : Prop :=
  (∀ s, MemLp (ψ.value s) 2) ∧
  (∀ s i a, MemLp (ψ.gradient s i a) 2) ∧
  (∀ s i a (φ : Configuration N → ℝ),
    ContDiff ℝ ∞ φ → HasCompactSupport φ →
    (∫ x, ψ.value s x * Complex.ofReal (lineDeriv ℝ φ x (direction i a))) =
      -(∫ x, ψ.gradient s i a x * (φ x : ℂ))) ∧
  (∀ (π : Equiv.Perm (Fin N)) s, ∀ᵐ x,
    ψ.value (s ∘ π) (x ∘ π) =
      (((Equiv.Perm.sign π : ℤ) : ℂ) * ψ.value s x)) ∧
  (∑ s : Spins N, ∫ x, ‖ψ.value s x‖ ^ 2) = 1 ∧
  (∀ s i, Integrable (fun x => ‖ψ.value s x‖ ^ 2 / ‖x i‖)) ∧
  (∀ s i j, i ≠ j →
    Integrable (fun x => ‖ψ.value s x‖ ^ 2 / ‖x i - x j‖))

def formEnergy {N : ℕ} (Z : ℝ) (ψ : FormVector N) : ℝ :=
  (1 / 2 : ℝ) *
      (∑ s : Spins N, ∑ i : Fin N, ∑ a : Fin 3,
        (∫ x, ‖ψ.gradient s i a x‖ ^ 2)) -
    Z * (∑ s : Spins N, ∑ i : Fin N,
      (∫ x, ‖ψ.value s x‖ ^ 2 / ‖x i‖)) +
    (∑ s : Spins N, ∑ i : Fin N, ∑ j : Fin N,
      if i < j then (∫ x, ‖ψ.value s x‖ ^ 2 / ‖x i - x j‖) else 0)

def energy (Z : ℝ) (N : ℕ) : ℝ :=
  if N = 0 then 0 else sInf {e | ∃ ψ : FormVector N,
    FormAdmissible ψ ∧ formEnergy Z ψ = e}

def ionization (m Z : ℕ) : ℝ :=
  energy Z (Z - m) - energy Z Z

def tfKinetic : ℝ := (3 / 10 : ℝ) * (3 * Real.pi ^ 2) ^ (2 / 3 : ℝ)

def directIntegrand (ρ : Space → ℝ) (p : Space × Space) : ℝ :=
  ρ p.1 * ρ p.2 / ‖p.1 - p.2‖

def TFAdmissible (M : ℝ) (ρ : Space → ℝ) : Prop :=
  (∀ᵐ x, 0 ≤ ρ x) ∧ Integrable ρ ∧ (∫ x, ρ x) = M ∧
  Integrable (fun x => ρ x ^ (5 / 3 : ℝ)) ∧
  Integrable (fun x => ρ x / ‖x‖) ∧ Integrable (directIntegrand ρ)

def tfFunctional (Z : ℝ) (ρ : Space → ℝ) : ℝ :=
  tfKinetic * (∫ x, ρ x ^ (5 / 3 : ℝ)) - Z * (∫ x, ρ x / ‖x‖) +
    (1 / 2 : ℝ) * ∫ p, directIntegrand ρ p

def tfEnergy (Z M : ℝ) : ℝ :=
  sInf {e | ∃ ρ : Space → ℝ, TFAdmissible M ρ ∧ tfFunctional Z ρ = e}

def tfIonization (m Z : ℝ) : ℝ := tfEnergy Z (Z - m) - tfEnergy Z Z

def TFCharacterization (a : ℝ) : Prop :=
  ∀ m : ℝ, 0 < m →
    Tendsto (tfIonization m) atTop (𝓝 (a * m ^ (7 / 3 : ℝ)))

def JointLimit (a : ℝ) : Prop :=
  ∀ m Z : ℕ → ℕ, (∀ j, 1 ≤ m j ∧ m j < Z j) →
    Tendsto m atTop atTop →
    Tendsto (fun j => (Z j : ℝ) / (m j : ℝ)) atTop atTop →
    Tendsto (fun j => ionization (m j) (Z j) / (m j : ℝ) ^ (7 / 3 : ℝ))
      atTop (𝓝 a)

def IteratedLimits (a : ℝ) : Prop :=
  Tendsto (fun m : ℕ => (limsup (ionization m) atTop) / (m : ℝ) ^ (7 / 3 : ℝ))
    atTop (𝓝 a) ∧
  Tendsto (fun m : ℕ => (liminf (ionization m) atTop) / (m : ℝ) ^ (7 / 3 : ℝ))
    atTop (𝓝 a)

def MainStatement : Prop :=
  ∃ a : ℝ, 0 < a ∧ TFCharacterization a ∧ JointLimit a ∧ IteratedLimits a

theorem generalized_ionization : MainStatement := by
  sorry

end CoulombAtom

end

end OAI
