import Mathlib

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped BigOperators Topology ContDiff

namespace NeutralAtom

abbrev Position := EuclideanSpace ℝ (Fin 3)
abbrev Configuration (n : ℕ) := Fin n → Position
abbrev Spins (n : ℕ) := Fin n → Fin 2
abbrev Wavefunction (n : ℕ) := Spins n → Configuration n → ℂ
abbrev Gradient (n : ℕ) := Spins n → Fin n → Fin 3 → Configuration n → ℂ

def coordinateDirection {n : ℕ} (i : Fin n) (a : Fin 3) : Configuration n :=
  Pi.single i (EuclideanSpace.single a 1)

def HasWeakGradient {n : ℕ} (ψ : Wavefunction n) (g : Gradient n) : Prop :=
  ∀ σ i a (φ : Configuration n → ℝ), ContDiff ℝ ∞ φ → HasCompactSupport φ →
    (∫ x, (fderiv ℝ φ x (coordinateDirection i a) : ℂ) * ψ σ x) =
      -(∫ x, (φ x : ℂ) * g σ i a x)

def IsAntisymmetric {n : ℕ} (ψ : Wavefunction n) : Prop :=
  ∀ (p : Equiv.Perm (Fin n)) (σ : Spins n),
    (fun x : Configuration n => ψ (σ ∘ p) (x ∘ p)) =ᵐ[volume]
      (fun x => (((Equiv.Perm.sign p : ℤ) : ℂ)) * ψ σ x)

def FormDomain {n : ℕ} (ψ : Wavefunction n) (g : Gradient n) : Prop :=
  IsAntisymmetric ψ ∧ HasWeakGradient ψ g ∧
  (∀ σ, MemLp (ψ σ) 2 volume) ∧
  (∀ σ i a, MemLp (g σ i a) 2 volume) ∧
  (∀ σ i, Integrable (fun x : Configuration n => ‖x i‖⁻¹ * ‖ψ σ x‖ ^ 2)) ∧
  (∀ σ i j, i < j →
    Integrable (fun x : Configuration n => ‖x i - x j‖⁻¹ * ‖ψ σ x‖ ^ 2))

def normSquared {n : ℕ} (ψ : Wavefunction n) : ℝ :=
  ∑ σ : Spins n, ∫ x : Configuration n, ‖ψ σ x‖ ^ 2

def coulombPotential {n : ℕ} (Z : ℕ) (x : Configuration n) : ℝ :=
  -(Z : ℝ) * (∑ i : Fin n, ‖x i‖⁻¹) +
    ∑ i : Fin n, ∑ j ∈ Finset.univ.filter (fun j : Fin n => i < j), ‖x i - x j‖⁻¹

def energy {n : ℕ} (Z : ℕ) (ψ : Wavefunction n) (g : Gradient n) : ℝ :=
  (1 / 2 : ℝ) * (∑ σ : Spins n, ∑ i : Fin n, ∑ a : Fin 3,
    ∫ x : Configuration n, ‖g σ i a x‖ ^ 2) +
  ∑ σ : Spins n, ∫ x : Configuration n, coulombPotential Z x * ‖ψ σ x‖ ^ 2

def IsNormalizedGroundState (Z : ℕ) (ψ : Wavefunction Z) : Prop :=
  ∃ g : Gradient Z, FormDomain ψ g ∧ normSquared ψ = 1 ∧
    ∀ (χ : Wavefunction Z) (h : Gradient Z),
      FormDomain χ h → normSquared χ = 1 → energy Z ψ g ≤ energy Z χ h

def density {N : ℕ} (ψ : Wavefunction (N + 1)) (x : Position) : ℝ :=
  (N + 1 : ℝ) * ∑ σ : Spins (N + 1),
    ∫ y : Configuration N, ‖ψ σ (Fin.cons x y)‖ ^ 2

def exteriorMass {N : ℕ} (ψ : Wavefunction (N + 1)) (r : ℝ) : ℝ :=
  ∫ x in {x : Position | r < ‖x‖}, density ψ x

def radius {N : ℕ} (ψ : Wavefunction (N + 1)) (m : ℕ) : ℝ :=
  sInf {r : ℝ | 0 ≤ r ∧ exteriorMass ψ r ≤ (m : ℝ)}

def bTF : ℝ := (81 * Real.pi ^ 2 / 2) ^ (1 / 3 : ℝ)

def largeCharge (m : ℕ) : Filter ℕ :=
  atTop ⊓ Filter.principal {N : ℕ | m < N + 1}

def upperRadius (Ψ : ∀ N : ℕ, Wavefunction (N + 1)) (m : ℕ) : EReal :=
  Filter.limsup (fun N : ℕ => (radius (Ψ N) m : EReal)) (largeCharge m)

def lowerRadius (Ψ : ∀ N : ℕ, Wavefunction (N + 1)) (m : ℕ) : EReal :=
  Filter.liminf (fun N : ℕ => (radius (Ψ N) m : EReal)) (largeCharge m)

theorem generalized_outer_radii
    (Ψ : ∀ N : ℕ, Wavefunction (N + 1))
    (hΨ : ∀ N : ℕ, IsNormalizedGroundState (N + 1) (Ψ N)) :
    Tendsto (fun m : ℕ => (((m : ℝ) ^ (1 / 3 : ℝ) : ℝ) : EReal) * upperRadius Ψ m)
      atTop (𝓝 (bTF : EReal)) ∧
    Tendsto (fun m : ℕ => (((m : ℝ) ^ (1 / 3 : ℝ) : ℝ) : EReal) * lowerRadius Ψ m)
      atTop (𝓝 (bTF : EReal)) := by
  sorry

end NeutralAtom
end

end OAI
