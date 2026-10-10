import Mathlib

namespace OAI

noncomputable section
open scoped BigOperators
open MeasureTheory intervalIntegral
open Finset
open Finset Nat ArithmeticFunction
open scoped ArithmeticFunction.Moebius
open Filter

namespace OrdinaryCorrelations

def OneBounded (f : ℕ → ℂ) : Prop := ∀ n, ‖f n‖ ≤ 1

def Multiplicative (f : ℕ → ℂ) : Prop :=
  ∀ m n : ℕ, 0 < m → 0 < n → m.Coprime n → f (m * n) = f m * f n

def distanceSq (f : ℕ → ℂ) {q : ℕ} (χ : DirichletCharacter ℂ q)
    (t X : ℝ) : ℝ :=
  ∑ p ∈ (Finset.Icc 2 ⌊X⌋₊).filter Nat.Prime,
    (1 - (f p * star (χ (p : ZMod q) *
      Complex.exp ((t * Real.log (p : ℝ) : ℝ) * Complex.I))).re) / (p : ℝ)

def distance (f : ℕ → ℂ) {q : ℕ} (χ : DirichletCharacter ℂ q)
    (t X : ℝ) : ℝ := Real.sqrt (distanceSq f χ t X)

def UniformlyNonpretentious (f : ℕ → ℂ) : Prop :=
  ∀ (q : ℕ), 0 < q → ∀ χ : DirichletCharacter ℂ q,
    Tendsto (fun N : ℕ => sInf ((fun t : ℝ => distance f χ t (N : ℝ)) ''
      Set.Icc (-(N : ℝ)) (N : ℝ))) atTop atTop

def shiftAverage (f₁ f₂ : ℕ → ℂ) (h₁ h₂ N : ℕ) : ℂ :=
  (N : ℂ)⁻¹ * ∑ n ∈ Finset.Icc 1 N, f₁ (n + h₁) * f₂ (n + h₂)

def affineAverage (f₁ f₂ : ℕ → ℂ) (a₁ a₂ b₁ b₂ N : ℕ) : ℂ :=
  (N : ℂ)⁻¹ * ∑ n ∈ Finset.Icc 1 N, f₁ (a₁ * n + b₁) * f₂ (a₂ * n + b₂)

def progressionAverage (f₁ f₂ : ℕ → ℂ) (h₁ h₂ l : ℕ) (b : ℤ)
    (X : ℝ) : ℂ :=
  (X : ℂ)⁻¹ * ∑ n ∈ (Finset.Icc 1 ⌊X⌋₊).filter
    (fun (n : ℕ) => (n : ℤ) ≡ b [ZMOD (l : ℤ)]), f₁ (n + h₁) * f₂ (n + h₂)

def liouville (n : ℕ) : ℝ := (ArithmeticFunction.liouville n : ℝ)

def affineLiouvilleSum (a₁ a₂ b₁ b₂ : ℕ) (X : ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 ⌊X⌋₊, liouville (a₁ * n + b₁) * liouville (a₂ * n + b₂)

def progressionLiouvilleSum (h l : ℕ) (b : ℤ) (X : ℝ) : ℝ :=
  ∑ n ∈ (Finset.Icc 1 ⌊X⌋₊).filter
    (fun (n : ℕ) => (n : ℤ) ≡ b [ZMOD (l : ℤ)]), liouville n * liouville (n + h)

def BinaryCorrectedElliott : Prop :=
  ∀ f₁ f₂ : ℕ → ℂ, OneBounded f₁ → OneBounded f₂ →
    Multiplicative f₁ → Multiplicative f₂ →
    (UniformlyNonpretentious f₁ ∨ UniformlyNonpretentious f₂) →
    ∀ h₁ h₂ : ℕ, h₁ ≠ h₂ →
      Tendsto (shiftAverage f₁ f₂ h₁ h₂) atTop (nhds 0)

def AffineElliott : Prop :=
  ∀ f₁ f₂ : ℕ → ℂ, OneBounded f₁ → OneBounded f₂ →
    Multiplicative f₁ → Multiplicative f₂ →
    (UniformlyNonpretentious f₁ ∨ UniformlyNonpretentious f₂) →
    ∀ a₁ a₂ b₁ b₂ : ℕ, 0 < a₁ → 0 < a₂ → a₁ * b₂ ≠ a₂ * b₁ →
      Tendsto (affineAverage f₁ f₂ a₁ a₂ b₁ b₂) atTop (nhds 0)

def ProgressionElliott : Prop :=
  ∀ f₁ f₂ : ℕ → ℂ, OneBounded f₁ → OneBounded f₂ →
    Multiplicative f₁ → Multiplicative f₂ →
    (UniformlyNonpretentious f₁ ∨ UniformlyNonpretentious f₂) →
    ∀ h₁ h₂ l : ℕ, h₁ ≠ h₂ → 0 < l → ∀ b : ℤ,
      Tendsto (progressionAverage f₁ f₂ h₁ h₂ l b) atTop (nhds 0)

def AffineLiouvilleLogSaving : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ a₁ a₂ b₁ b₂ : ℕ, 0 < a₁ → 0 < a₂ →
    a₁ * b₂ ≠ a₂ * b₁ → ∃ C : ℝ, ∀ X : ℝ, 3 ≤ X →
      |affineLiouvilleSum a₁ a₂ b₁ b₂ X| ≤ C * X / (Real.log X) ^ c

def ProgressionLiouvilleLogSaving : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ h l : ℕ, 0 < h → 0 < l → ∃ C : ℝ,
    ∀ (b : ℤ) (X : ℝ), 3 ≤ X →
      |progressionLiouvilleSum h l b X| ≤ C * X / (Real.log X) ^ c

end OrdinaryCorrelations

end

end OAI
