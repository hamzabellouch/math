import Mathlib.Data.Int.Interval
import Mathlib.Basic.Real.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic

namespace OAI

open MeasureTheory
open scoped ENNReal lp ComplexConjugate

noncomputable section

namespace InvariantProjection.ConditionalConvolution

def window (K : ℕ) (n : ℕ) : Finset ℤ :=
  (Finset.Icc (-(K : ℤ)) (K : ℤ)).filter fun v => |(n : ℤ) + v| ≤ (K : ℤ)

def selector (K : ℕ) (n : ℕ) (v : ℤ) : ℤ :=
  if (K : ℤ) < |v| then v else (n : ℤ) + v

def omittedEvent {Ω : Type*} (H : ℤ → Set Ω) (K : ℕ) (n : ℕ) (v : ℤ) : Set Ω :=
  if v ∈ window K n then ∅ else H (selector K n v)

def truncated (K : ℕ) (n : ℕ) (A B : ℤ → ℂ) : ℂ :=
  ∑ v ∈ window K n, A v * B (-(n : ℤ) - v)

def coeffA {Ω : Type*} (ξ : Ω → ℓ²(ℤ, ℂ)) (Fx : Ω → ℤ → ℝ)
    (ω : Ω) (v : ℤ) : ℂ := ξ ω v / (Fx ω v : ℂ)

def coeffB {Ω : Type*} (γ : Ω → ℓ²(ℤ, ℂ)) (Fy : Ω → ℤ → ℝ)
    (ω : Ω) (w : ℤ) : ℂ := (Fy ω (-w) : ℂ) * conj (γ ω (-w))

structure Data (Ω : Type*) [mΩ : MeasurableSpace Ω] (μ : Measure Ω)
    (K : ℕ) (D a c η δ : ℝ) where
  mX : MeasurableSpace Ω
  mY : MeasurableSpace Ω
  mX_le : mX ≤ mΩ
  mY_le : mY ≤ mΩ
  ξ : Ω → ℓ²(ℤ, ℂ)
  γ : Ω → ℓ²(ℤ, ℂ)
  ξ_measurable : StronglyMeasurable[mX] ξ
  γ_measurable : StronglyMeasurable[mY] γ
  ξ_unit : ∀ᵐ ω ∂μ, ‖ξ ω‖ ≤ 1
  γ_unit : ∀ᵐ ω ∂μ, ‖γ ω‖ ≤ 1
  Fx : Ω → ℤ → ℝ
  Fy : Ω → ℤ → ℝ
  Fx_measurable : ∀ k, Measurable[mΩ] (fun ω => Fx ω k)
  Fy_measurable : ∀ k, Measurable[mΩ] (fun ω => Fy ω k)
  Fx_pos : ∀ᵐ ω ∂μ, ∀ k, 0 < Fx ω k
  Fy_pos : ∀ᵐ ω ∂μ, ∀ k, 0 < Fy ω k
  Fx_zero : ∀ᵐ ω ∂μ, Fx ω 0 = 1
  Fy_zero : ∀ᵐ ω ∂μ, Fy ω 0 = 1
  zero_convolution : ∀ n : ℕ, n ≤ 2 * K → ∀ᵐ ω ∂μ,
    (∑' v : ℤ, coeffA ξ Fx ω v * coeffB γ Fy ω (-(n : ℤ) - v)) = 0
  ratio_bounds : ∀ n : ℕ, n ≤ 2 * K → ∀ᵐ ω ∂μ, ∀ v : ℤ,
    0 < Fy ω ((n : ℤ) + v) / Fx ω v ∧
    Fy ω ((n : ℤ) + v) / Fx ω v ≤
      min (Fy ω v / Fx ω v) (Fy ω ((n : ℤ) + v) / Fx ω ((n : ℤ) + v)) ∧
    min (Fy ω v / Fx ω v) (Fy ω ((n : ℤ) + v) / Fx ω ((n : ℤ) + v)) ≤ 1
  E : Set Ω
  E_measurable : MeasurableSet[mΩ] E
  E_mass : c ≤ μ.real E
  coefficient_bounds : ∀ᵐ ω ∂μ.restrict E,
    (∀ v : ℤ, |v| ≤ (K : ℤ) → ‖coeffA ξ Fx ω v‖ ≤ D) ∧
    (∀ v : ℤ, |v| ≤ (K : ℤ) → ‖coeffB γ Fy ω v‖ ≤ D) ∧
    a ≤ ‖coeffA ξ Fx ω 0‖ ∧ a ≤ ‖coeffB γ Fy ω 0‖
  H₁ : ℤ → Set Ω
  H₂ : ℤ → Set Ω
  H₁_measurable : ∀ k, MeasurableSet[mΩ] (H₁ k)
  H₂_measurable : ∀ k, MeasurableSet[mΩ] (H₂ k)
  attenuation : ∀ᵐ ω ∂μ.restrict E, ∀ k : ℤ, (K : ℤ) < |k| →
    Fy ω k / Fx ω k ≤ η + (H₁ k).indicator (fun _ => (1 : ℝ)) ω +
      (H₂ k).indicator (fun _ => (1 : ℝ)) ω
  conditional₁ : ∀ k : ℤ, (K : ℤ) < |k| →
    μ[(H₁ k).indicator (fun _ => (1 : ℝ)) | mX] ≤ᵐ[μ] fun _ => δ
  conditional₂ : ∀ k : ℤ, (K : ℤ) < |k| →
    μ[(H₂ k).indicator (fun _ => (1 : ℝ)) | mY] ≤ᵐ[μ] fun _ => δ

end InvariantProjection.ConditionalConvolution

end

end OAI
