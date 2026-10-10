import Mathlib
import OAI.Combinatorics.KMedian.Geometry.ComputedRationalCompression

namespace OAI

namespace MetricKMedian.IntegerLaw
open Finset

def compressRational {n d : ℕ} (μ : IntegerLaw (Fin n)) (v : Fin n → Fin d → ℚ)
    (L : ℕ) (hnum : ∀ i j, |(v i j).num| ≤ (2:ℤ)^L)
    (hden : ∀ i j, ((v i j).den:ℤ) ≤ (2:ℤ)^L) : IntegerLaw (Fin n) :=
  μ.computedCompress (RationalLaw.scaledFeatures v) (L*(n+1))
    (RationalLaw.scaledFeatures_bound v L hnum hden)

theorem compressRational_spec {n d : ℕ} (μ : IntegerLaw (Fin n))
    (v : Fin n → Fin d → ℚ) (L : ℕ)
    (hnum : ∀ i j, |(v i j).num| ≤ (2:ℤ)^L)
    (hden : ∀ i j, ((v i j).den:ℤ) ≤ (2:ℤ)^L) :
    let ν := μ.compressRational v L hnum hden
    ν.denominator ≤ μ.denominator*(2:ℤ)^(((2*(d+1)*(d+1+L*(n+1)))*(n+1))*n) ∧
      ν.support ⊆ μ.support ∧ ν.support.card ≤ d+1 ∧
      ∀ j, (∑ i, ν.rational.weight i*v i j)=∑ i, μ.rational.weight i*v i j := by
  have hh := μ.computedCompress_spec (RationalLaw.scaledFeatures v) (L*(n+1))
    (RationalLaw.scaledFeatures_bound v L hnum hden)
  refine ⟨hh.1,hh.2.1,hh.2.2.1,?_⟩
  intro j
  let D := RationalScaling.denominator (fun i => v i j)
  have hD : (D:ℚ) ≠ 0 := by
    exact_mod_cast (RationalScaling.denominator_pos (fun i => v i j)).ne'
  have hcast : ∀ i, (RationalLaw.scaledFeatures v i j:ℚ)=v i j*(D:ℚ) := by
    intro i
    rw [RationalLaw.scaledFeatures_eq]
    exact RationalScaling.numerator_cast _ i
  have hm := hh.2.2.2 j
  simp only [hcast,← mul_assoc,← sum_mul] at hm
  exact mul_right_cancel₀ hD hm

end MetricKMedian.IntegerLaw

end OAI
