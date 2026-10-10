import OAI.Probability.InvariantIsing.Haar.Rotation
import OAI.Probability.IsingPerceptron.ArraySynchronization

namespace OAI

/-!
# Spectral overlap geometry

The finite projected overlaps are Gram matrices. Panchenko's ultrametricity
theorem applies to their limit arrays satisfying the Ghirlanda–Guerra identities.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators Matrix

namespace InvariantIsing

/-- Overlap restricted to a deterministic spectral coordinate group. -/
def projectedOverlap {N : ℕ} (U : Rotation N) (I : Finset (Fin N))
    (σ τ : Spin N) : ℝ :=
  (N : ℝ)⁻¹ * ∑ i ∈ I, U (spinVector σ) i * U (spinVector τ) i

lemma projectedOverlap_symm {N : ℕ} (U : Rotation N) (I : Finset (Fin N))
    (σ τ : Spin N) : projectedOverlap U I σ τ = projectedOverlap U I τ σ := by
  simp only [projectedOverlap, mul_comm]

/-- Each spectral overlap component is a positive semidefinite Gram kernel. -/
lemma projectedOverlap_posSemidef {N m : ℕ} (U : Rotation N) (I : Finset (Fin N))
    (σ : Fin m → Spin N) :
    Matrix.PosSemidef (fun i j => projectedOverlap U I (σ i) (σ j)) := by
  classical
  let A : Matrix (Fin m) (Fin N) ℝ := fun i k =>
    if k ∈ I then U (spinVector (σ i)) k else 0
  have hp := (Matrix.posSemidef_self_mul_conjTranspose A).smul
    (show (0 : ℝ) ≤ (N : ℝ)⁻¹ by positivity)
  have he : (fun i j : Fin m => projectedOverlap U I (σ i) (σ j)) =
      (N : ℝ)⁻¹ • (A * Aᴴ) := by
    ext i j
    change (N : ℝ)⁻¹ * (∑ k ∈ I, U (spinVector (σ i)) k * U (spinVector (σ j)) k) =
      (N : ℝ)⁻¹ * ∑ k, (if k ∈ I then U (spinVector (σ i)) k else 0) *
        (if k ∈ I then U (spinVector (σ j)) k else 0)
    congr 1
    simp only [ite_mul, mul_ite, zero_mul, mul_zero,
      Finset.sum_ite_mem, Finset.univ_inter, Finset.inter_self]
  rw [he]
  exact hp

lemma projectedOverlap_self_nonneg {N : ℕ} (U : Rotation N) (I : Finset (Fin N))
    (σ : Spin N) : 0 ≤ projectedOverlap U I σ σ := by
  apply mul_nonneg (by positivity)
  exact Finset.sum_nonneg fun i _ => mul_self_nonneg _

/-- Full spectral overlap agrees with the ordinary spin overlap, because an
orthogonal rotation preserves the inner product. -/
lemma projectedOverlap_univ {N : ℕ} (U : Rotation N) (σ τ : Spin N) :
    projectedOverlap U Finset.univ σ τ =
      (N : ℝ)⁻¹ * ∑ i, spinValue (σ i) * spinValue (τ i) := by
  simp only [projectedOverlap]
  congr 1
  have h := U.inner_map_map (spinVector σ) (spinVector τ)
  simpa only [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, star_trivial,
    spinVector_apply, RCLike.inner_apply, starRingEnd_apply, star_trivial, mul_comm] using h

/-- Panchenko (2013), Theorem 1, in the exact bounded-Gram-array specialization
needed after proving GG for spectral overlap limits. The proof is already in
`IsingPerceptron.gg_ultrametric`; GG remains an explicit hypothesis here. -/
theorem ultrametric_of_gram_gg {Ω : Type*} [MeasurableSpace Ω]
    {B : Ω → IsingPerceptron.RealArray} {μ : Measure Ω} [IsProbabilityMeasure μ]
    (hB : Measurable B) (hsym : ∀ ω i j, B ω i j = B ω j i)
    (hwe : IsingPerceptron.WeaklyExchangeable B μ)
    (hgg : IsingPerceptron.HasGhirlandaGuerra B μ) {D : ℝ}
    (hgram : ∀ ω n, Matrix.PosSemidef (IsingPerceptron.arrayBlock B n ω))
    (hdiag : ∀ ω i, B ω i i = D) :
    ∀ᵐ ω ∂μ, IsingPerceptron.IsUltrametricArray (B ω) :=
  IsingPerceptron.gg_ultrametric hB hsym hwe hgg hgram hdiag

end InvariantIsing

end

end OAI
