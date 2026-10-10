import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingPolynomialTimeBound
import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingPolynomialLimit

namespace OAI

/-! # Uniform physical time control for the actual infinite Fourier series -/

open Set Filter Topology

namespace DefocusingNLS

local notation "E" => EuclideanSpace ℝ (Fin 12)

theorem expandingPhysical_time_bound (a b k L T M G : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (hL : 1 ≤ L) (hT : 0 ≤ T)
    (u : C(Icc (0 : ℝ) T, FourierL2)) (g : ℝ → FourierL2)
    (hu : ∀ s, ‖u s‖ ≤ M) (hg : ∀ s ∈ Icc 0 T, ‖g s‖ ≤ G)
    (hmode : ∀ t ∈ Ioo 0 T, ∀ n : frequencyLattice,
      HasDerivAt (fun τ => expandingFourierCoefficient a (k + 2) (expandingRadius L τ) (u (projIcc 0 T hT τ)) n)
        (expandingModeRate a b L t n * expandingFourierCoefficient a (k + 2) (expandingRadius L t)
          (u (projIcc 0 T hT t)) n + expandingFourierCoefficient a (k + 2) (expandingRadius L t) (g t) n) t)
    (y : E) (s t : Icc (0 : ℝ) T) :
    ‖expandingTorusFunction a (k + 2) (expandingRadius L t) (u t)
        (euclideanToTorus ((expandingRadius L t)⁻¹ • y)) -
      expandingTorusFunction a (k + 2) (expandingRadius L s) (u s)
        (euclideanToTorus ((expandingRadius L s)⁻¹ • y))‖ ≤
      ((|a| + |b| + 1 + ‖y‖ / 2) * expandingJetBound a k * M +
        expandingEmbeddingBound a (k + 2) * G) * |(t : ℝ) - s| := by
  have ht := tendsto_expandingPhysicalPolynomial a (k + 2) L T ha ha1 (by linarith) hL hT u y t
  have hs := tendsto_expandingPhysicalPolynomial a (k + 2) L T ha ha1 (by linarith) hL hT u y s
  exact le_of_tendsto (ht.sub hs).norm (Filter.Eventually.of_forall (fun S =>
    expandingPhysicalPolynomial_time_bound a b k L T M G ha ha1 hk hL hT u g hu hg hmode S y s t s.2 t.2))

theorem expandingMild_physical_time_bound (a b k L T M G : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (hL : 1 ≤ L) (hT : 0 ≤ T)
    (u : C(Icc (0 : ℝ) T, FourierL2)) (g : ℝ → FourierL2) (f : FourierL2)
    (hgcont : ContinuousOn g (Icc 0 T))
    (hsol : ∀ s : Icc (0 : ℝ) T,
      u s = expandingFreeStep a b (k + 2) L s ha (by linarith) hL s.2.1 f +
        expandingDuhamel a b (k + 2) L ha (by linarith) hL s g)
    (hu : ∀ s, ‖u s‖ ≤ M) (hg : ∀ s ∈ Icc 0 T, ‖g s‖ ≤ G)
    (y : E) (s t : Icc (0 : ℝ) T) :
    ‖expandingTorusFunction a (k + 2) (expandingRadius L t) (u t)
        (euclideanToTorus ((expandingRadius L t)⁻¹ • y)) -
      expandingTorusFunction a (k + 2) (expandingRadius L s) (u s)
        (euclideanToTorus ((expandingRadius L s)⁻¹ • y))‖ ≤
      ((|a| + |b| + 1 + ‖y‖ / 2) * expandingJetBound a k * M +
        expandingEmbeddingBound a (k + 2) * G) * |(t : ℝ) - s| := by
  apply expandingPhysical_time_bound a b k L T M G ha ha1 hk hL hT u g hu hg
  intro τ hτ n
  apply hasDerivAt_expandingMild_coefficient a b (k + 2) L T ha (by linarith) hL
    (fun τ => u (projIcc 0 T hT τ)) g f hgcont
  · intro σ hσ
    rw [projIcc_of_mem hT hσ]
    exact hsol ⟨σ, hσ⟩
  · exact hτ

end DefocusingNLS

end OAI
