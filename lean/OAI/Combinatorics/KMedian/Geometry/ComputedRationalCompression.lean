import Mathlib
import OAI.Combinatorics.KMedian.Compression.ComputedCompression
import OAI.Combinatorics.KMedian.Compression.RationalIntegerLaw

namespace OAI

namespace MetricKMedian.RationalLaw
open Finset

def scaledFeatures {n d : ℕ} (v : Fin n → Fin d → ℚ) : Fin n → Fin d → ℤ :=
  let M := Vector.ofFn (fun i => Vector.ofFn (fun j => RationalScaling.numerator (fun i => v i j) i))
  fun i j => M[i.val][j.val]

@[simp] theorem scaledFeatures_eq {n d : ℕ} (v : Fin n → Fin d → ℚ)
    (i : Fin n) (j : Fin d) :
    scaledFeatures v i j=RationalScaling.numerator (fun i => v i j) i := by
  simp only [scaledFeatures,Vector.getElem_ofFn]

theorem scaledFeatures_bound {n d : ℕ} (v : Fin n → Fin d → ℚ) (L : ℕ)
    (hnum : ∀ i j, |(v i j).num| ≤ (2:ℤ)^L)
    (hden : ∀ i j, ((v i j).den:ℤ) ≤ (2:ℤ)^L) :
    ∀ i j, |scaledFeatures v i j| ≤ (2:ℤ)^(L*(n+1)) := by
  intro i j
  rw [scaledFeatures_eq]
  simpa only [Fintype.card_fin] using RationalScaling.numerator_bound (fun i => v i j) L
    (fun i => hnum i j) (fun i => hden i j) i

def computedCompress {n d : ℕ} (μ : RationalLaw (Fin n)) (v : Fin n → Fin d → ℚ)
    (L : ℕ) (hnum : ∀ i j, |(v i j).num| ≤ (2:ℤ)^L)
    (hden : ∀ i j, ((v i j).den:ℤ) ≤ (2:ℤ)^L) : IntegerLaw (Fin n) :=
  μ.integer.computedCompress (scaledFeatures v) (L*(n+1))
    (scaledFeatures_bound v L hnum hden)

theorem computedCompress_spec {n d : ℕ} (μ : RationalLaw (Fin n))
    (v : Fin n → Fin d → ℚ) (L W : ℕ)
    (hnum : ∀ i j, |(v i j).num| ≤ (2:ℤ)^L)
    (hden : ∀ i j, ((v i j).den:ℤ) ≤ (2:ℤ)^L)
    (hμden : ∀ i, ((μ.weight i).den:ℤ) ≤ (2:ℤ)^W) :
    let ν := computedCompress μ v L hnum hden
    ν.denominator ≤ (2:ℤ)^(W*n+((2*(d+1)*(d+1+L*(n+1)))*(n+1))*n) ∧
      ν.support.card ≤ d+1 ∧
      (∀ i, μ.weight i=0 → ν.numerator i=0) ∧
      ∀ j, (∑ i, ν.rational.weight i*v i j)=∑ i, μ.weight i*v i j := by
  dsimp only [computedCompress]
  let ν := μ.integer.computedCompress (scaledFeatures v) (L*(n+1))
    (scaledFeatures_bound v L hnum hden)
  have hh := μ.integer.computedCompress_spec (scaledFeatures v) (L*(n+1))
    (scaledFeatures_bound v L hnum hden)
  refine ⟨?_,hh.2.2.1,?_,?_⟩
  · have hD : μ.integer.denominator ≤ (2:ℤ)^(W*n) := by
      simpa only [integer,Fintype.card_fin] using RationalScaling.denominator_bound μ.weight W hμden
    apply hh.1.trans
    calc
      _ ≤ (2:ℤ)^(W*n)*(2:ℤ)^(((2*(d+1)*(d+1+L*(n+1)))*(n+1))*n) :=
        mul_le_mul_of_nonneg_right hD (by positivity)
      _ = _ := by rw [← pow_add]
  · intro i hi
    by_contra hn
    have hm := hh.2.1 ((ν.mem_support i).mpr hn)
    exact ((μ.integer_support_mem i).mp hm) hi
  · intro j
    let D := RationalScaling.denominator (fun i => v i j)
    have hD : (D:ℚ) ≠ 0 := by exact_mod_cast (RationalScaling.denominator_pos (fun i => v i j)).ne'
    have hcast : ∀ i, (scaledFeatures v i j:ℚ)=v i j*(D:ℚ) := by
      intro i
      rw [scaledFeatures_eq]
      exact RationalScaling.numerator_cast _ i
    have hm := hh.2.2.2 j
    simp only [hcast,μ.integer_weight,← mul_assoc,← sum_mul] at hm
    exact mul_right_cancel₀ hD hm

end MetricKMedian.RationalLaw

end OAI
