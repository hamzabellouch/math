import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingPhysicalPolynomial
import OAI.MathematicalPhysics.DefocusingNLS.Certificates.InteriorDerivativeLipschitz

namespace OAI

/-! # A uniform time modulus for finite physical Fourier sums -/

open Set

namespace DefocusingNLS

local notation "E" => EuclideanSpace ℝ (Fin 12)

theorem expandingPhysicalPolynomial_time_bound (a b k L T M G : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (hL : 1 ≤ L) (hT : 0 ≤ T)
    (u : C(Icc (0 : ℝ) T, FourierL2)) (g : ℝ → FourierL2)
    (hu : ∀ s, ‖u s‖ ≤ M) (hg : ∀ s ∈ Icc 0 T, ‖g s‖ ≤ G)
    (hmode : ∀ t ∈ Ioo 0 T, ∀ n : frequencyLattice,
      HasDerivAt (fun τ => expandingFourierCoefficient a (k + 2) (expandingRadius L τ) (u (projIcc 0 T hT τ)) n)
        (expandingModeRate a b L t n * expandingFourierCoefficient a (k + 2) (expandingRadius L t)
          (u (projIcc 0 T hT t)) n + expandingFourierCoefficient a (k + 2) (expandingRadius L t) (g t) n) t)
    (S : Finset frequencyLattice) (y : E) (s t : ℝ) (hs : s ∈ Icc 0 T) (ht : t ∈ Icc 0 T) :
    ‖expandingPhysicalPolynomial a (k + 2) L T hT u S y t -
        expandingPhysicalPolynomial a (k + 2) L T hT u S y s‖ ≤
      ((|a| + |b| + 1 + ‖y‖ / 2) * expandingJetBound a k * M +
        expandingEmbeddingBound a (k + 2) * G) * |t - s| := by
  let D := fun τ => ∑ n ∈ S,
    (physicalModeRate a b (expandingRadius L τ) n y *
      expandingFourierCoefficient a (k + 2) (expandingRadius L τ) (u (projIcc 0 T hT τ)) n +
      expandingFourierCoefficient a (k + 2) (expandingRadius L τ) (g τ) n) *
        spatialFourierCharacter n ((expandingRadius L τ)⁻¹ • y)
  apply norm_sub_le_of_interior_derivative _ D T _ hT
    (continuous_expandingPhysicalPolynomial a (k + 2) L T hL hT u S y)
    (fun τ hτ => hasDerivAt_expandingPhysicalPolynomial a b (k + 2) L T hL hT u g S y τ hτ (hmode τ hτ))
    ?_ s t hs ht
  intro τ hτ
  have hR : 1 ≤ expandingRadius L τ := hL.trans (expandingRadius_ge L τ hL hτ.1.le)
  have he := expandingPhysicalDerivative_sum_bound a b k (expandingRadius L τ) ha ha1 hk hR
    (u (projIcc 0 T hT τ)) (g τ) y S
  have hb := (norm_sum_le S _).trans he
  dsimp only [D]
  apply hb.trans
  apply add_le_add
  · exact mul_le_mul_of_nonneg_left (hu _) (by unfold expandingJetBound expandingEmbeddingBound; positivity)
  · exact mul_le_mul_of_nonneg_left (hg τ ⟨hτ.1.le, hτ.2.le⟩) (by unfold expandingEmbeddingBound; positivity)

end DefocusingNLS

end OAI
