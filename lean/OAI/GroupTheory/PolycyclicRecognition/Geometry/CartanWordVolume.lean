import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanSemidirectWords

namespace OAI

/-! # Upper volume of controlled word endpoints

The semidirect-product word estimate and the exact Haar volume of Cartan
boxes give a polynomial prefactor times the template support exponential.
This is an upper bound for the nilpotent coordinate of actual word endpoints.
-/

noncomputable section

namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule MeasureTheory
open scoped Manifold ENNReal

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {H : LieSubalgebra ℝ L} [H.IsCartanSubalgebra] (M : CartanWordModel H)
  {n : ℕ} (T : TriangularAdjoint L n)
  (hunimod : ∀ x : L, LinearMap.trace ℝ L (ad ℝ L x) = 0)
  {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  (eW : HeightSpace T.character ≃ₗ[ℝ] W)
  {EN N : Type*} [NormedAddCommGroup EN] [NormedSpace ℝ EN]
  [FiniteDimensional ℝ EN] [TopologicalSpace N] [ChartedSpace EN N] [Group N]
  [LieGroup (𝓘(ℝ, EN)) ⊤ N] [T2Space N]
  [SimplyConnectedSpace N] [MeasurableSpace N] [BorelSpace N]
  (eN : cartanRootIdeal H ≃ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, EN)) N)
  (ExpN : GroupLieAlgebra (𝓘(ℝ, EN)) N → N) (hExpN : IsGroupExponential ExpN)
  (hbijN : Function.Bijective ExpN) (dynkinN : NilpotentDynkinExpansionInput EN N)
  (haarN : NilpotentExponentialHaarInput EN N)
  {ED D : Type*} [NormedAddCommGroup ED] [NormedSpace ℝ ED]
  [FiniteDimensional ℝ ED] [TopologicalSpace D] [ChartedSpace ED D] [Group D]
  [LieGroup (𝓘(ℝ, ED)) ⊤ D] [T2Space D]
  (eD : H ≃ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, ED)) D)
  (ExpD : GroupLieAlgebra (𝓘(ℝ, ED)) D → D) (hExpD : IsGroupExponential ExpD)
  (hbijD : Function.Bijective ExpD) (dynkinD : NilpotentDynkinExpansionInput ED D)
  (φ : D →* MulAut N)

include hExpD dynkinD haarN in
/-- Every set of controlled nilpotent endpoint coordinates has the claimed
exponential upper rate, with a polynomial prefactor uniform in the template. -/
theorem exists_semidirect_word_volume_bound
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    (hφ : ∀ d, φ d = M.adjointGroupAutomorphism T eN ExpN hExpN hbijN dynkinN
      (cartanLog H eD ExpD hbijD d))
    {RN RD : ℝ} (hRN : 0 ≤ RN) (hRD : 0 ≤ RD) :
    ∃ (μ : Measure N) (C : ℝ) (q : ℕ), μ.IsHaarMeasure ∧ 0 ≤ C ∧
      ∀ {E : Set W}, IsCompact E → E.Nonempty → ∀ (γ : M.Bases) (r : ℝ), 0 ≤ r →
      ∀ (m : ℕ) (S : Set N),
      (∀ z ∈ S, ∃ (u : ℕ → N) (v : ℕ → D),
        (∀ i < m, u i ∈ exponentialCoordinateBox (ExpN ∘ eN)
          (WordBasisSelections.basis M.letter M.wordList γ) RN) ∧
        (∀ i < m, v i ∈ exponentialCoordinateBox (ExpD ∘ eD) (finBasis ℝ H) RD) ∧
        (∀ i < m, ∃ w ∈ E,
          eW (heightProjection T.character
            (cartanLog H eD ExpD hbijD (wordPrefix v i) : L)) = r • w) ∧
        (wordPrefix (fun i => (⟨u i, v i⟩ : N ⋊[φ] D)) m).left = z) →
      μ S ≤ ENNReal.ofReal C * ENNReal.ofReal (1 + (m : ℝ)) ^ q *
        ENNReal.ofReal (Real.exp (r * (M.supportIn T hunimod eW).templateSupport E)) := by
  obtain ⟨A, p, hA, hword⟩ := M.exists_semidirect_word_bound T hunimod eW eN ExpN hExpN
    hbijN dynkinN eD ExpD hExpD hbijD dynkinD φ b₀ hφ hRN hRD
  obtain ⟨μ, c, C, hμ, _, hC, hvol⟩ :=
    M.exists_groupBox_haar_bounds T hunimod eW eN ExpN hExpN haarN b₀
  let d := finrank ℝ (cartanRootIdeal H)
  refine ⟨μ, C * (2 * A) ^ d, p * d, hμ, by positivity, ?_⟩
  intro E hE hne γ r hr m S hS
  obtain ⟨β, hβ, _⟩ := M.exists_maximizing_box_basis T hunimod eW b₀ E
  have hsub : S ⊆ M.groupBox T hunimod eW (ExpN ∘ eN) E β r (A * (1 + (m : ℝ)) ^ p) := by
    intro z hz
    obtain ⟨u, v, hu, hv, hh, hprod⟩ := hS z hz
    rw [← hprod]
    exact hword hE hne β hβ γ r hr m u v hu hv hh
  apply (measure_mono hsub).trans
  apply ((hvol E β hβ r (A * (1 + (m : ℝ)) ^ p) (by positivity)).2).trans
  have he : 2 * (A * (1 + (m : ℝ)) ^ p) = (2 * A) * (1 + (m : ℝ)) ^ p := by ring
  rw [he, ENNReal.ofReal_mul (mul_nonneg (by norm_num) hA), mul_pow,
    ENNReal.ofReal_pow (by positivity), ← pow_mul,
    ENNReal.ofReal_mul hC.le, ENNReal.ofReal_pow (mul_nonneg (by norm_num) hA)]
  exact le_of_eq (by dsimp [d]; ring)

end PolycyclicRecognition.CartanWordModel

end

end OAI
