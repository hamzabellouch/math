import Mathlib

namespace OAI

noncomputable section

namespace Balanced.DeletionLaw

abbrev Offset (q n : ℕ) := Fin n → Fin q
abbrev Split (q n : ℕ) := Fin 2 → Offset q n
abbrev Weight (q n : ℕ) := Offset q n → Offset q n → Split q n → ℝ
abbrev DeletionSet (q n : ℕ) := Fin n → Finset (Fin q)

def IsSubprobabilityKernel {q n : ℕ} (κ : Weight q n) : Prop :=
  (∀ m₀ m₁ s, 0 ≤ κ m₀ m₁ s) ∧ (∀ m₀ m₁, ∑ s, κ m₀ m₁ s ≤ 1)

def deletionSet {q n : ℕ} (m₁ : Offset q n) (s : Split q n) : DeletionSet q n :=
  fun i => {m₁ i, s 0 i, s 1 i}

def DistinctOutput {q n : ℕ} (κ : Weight q n) : Prop :=
  ∀ m₀ m₁ s, 0 < κ m₀ m₁ s → ∀ i, (deletionSet m₁ s i).card = 3

def CylinderBound {q n : ℕ} (κ : Weight q n) (K : ℝ) : Prop :=
  ∀ m₀ m₁ (slots : Finset (Fin 2 × Fin n)) (prescribed : Fin 2 × Fin n → Fin q),
    (∑ s, if ∀ t ∈ slots, s t.1 t.2 = prescribed t then κ m₀ m₁ s else 0) ≤
      (K / q) ^ slots.card

def offsetAverage {q n : ℕ} (κ : Weight q n) (m₁ : Offset q n) (s : Split q n) : ℝ :=
  (∑ m₀, κ m₀ m₁ s) / (q : ℝ) ^ (2 * n)

def successMass {q n : ℕ} (κ : Weight q n) : ℝ :=
  ∑ m₁, ∑ s, offsetAverage κ m₁ s

def deletionMass {q n : ℕ} (κ : Weight q n) (D : DeletionSet q n) : ℝ :=
  ∑ m₁, ∑ s, if deletionSet m₁ s = D then offsetAverage κ m₁ s else 0

def conditionedDeletionMass {q n : ℕ} (κ : Weight q n) (D : DeletionSet q n) : ℝ :=
  deletionMass κ D / successMass κ

def uniformDeletionMass (q n : ℕ) : ℝ :=
  ((Nat.choose q 3 : ℝ) ^ n)⁻¹

def uniformDeletionLaw (q n : ℕ) (D : DeletionSet q n) : ℝ :=
  if ∀ i, (D i).card = 3 then uniformDeletionMass q n else 0

def FiniteDomination : Prop :=
  ∀ (q n : ℕ), 3 ≤ q → ∀ (κ : Weight q n) (K a₀ : ℝ),
    0 ≤ K → 0 < a₀ → IsSubprobabilityKernel κ → DistinctOutput κ →
    CylinderBound κ K → a₀ ≤ successMass κ →
    ∀ D : DeletionSet q n, (∀ i, (D i).card = 3) →
      conditionedDeletionMass κ D ≤
        a₀⁻¹ * K ^ (2 * n) * uniformDeletionMass q n

def ExponentialDomination : Prop :=
  ∀ (K a₀ : ℝ), 0 ≤ K → 0 < a₀ → ∃ C : ℝ, 0 < C ∧
    ∀ (q : ℕ), 3 ≤ q → ∀ κ : Weight q (q + 1),
      IsSubprobabilityKernel κ → DistinctOutput κ → CylinderBound κ K →
      a₀ ≤ successMass κ → ∀ D : DeletionSet q (q + 1),
        conditionedDeletionMass κ D ≤ Real.exp (C * q) * uniformDeletionLaw q (q + 1) D

end Balanced.DeletionLaw

end

end OAI
