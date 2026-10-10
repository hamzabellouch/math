import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanWordVolume

namespace OAI

/-! # Compact increments in the Cartan word model

Compact sets of increments have bounded logarithms in the published global
nilpotent exponential charts. This removes the coordinate-radius assumptions
from the semidirect word estimate and leaves ordinary compact step data.
-/

noncomputable section

namespace PolycyclicRecognition

open Module LieAlgebra LieModule
open scoped Manifold

/-- A compact subset has bounded coordinates in any global exponential chart,
without choosing a norm on the abstract Lie-algebra model. -/
theorem exists_compact_exponential_coordinate_bound
    {L : Type*} [LieRing L] [LieAlgebra ℝ L]
    {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace G] [ChartedSpace E G] [Group G] [LieGroup (𝓘(ℝ, E)) ⊤ G]
    (e : L ≃ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, E)) G)
    (Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G)
    (chart : GroupLieAlgebra (𝓘(ℝ, E)) G ≃ₜ G) (hchart : ∀ x, chart x = Exp x)
    {J : Type*} [Fintype J] (b : Basis J ℝ L) {K : Set G} (hK : IsCompact K) :
    ∃ R : ℝ, 0 ≤ R ∧ K ⊆ exponentialCoordinateBox (Exp ∘ e) b R := by
  let f := (b.equivFun.toLinearMap.comp e.symm.toLinearMap).toContinuousLinearMap
  have hc : Continuous (fun g => f (chart.symm g)) := f.continuous.comp chart.symm.continuous
  obtain ⟨R, hR⟩ := hK.exists_bound_of_continuousOn hc.continuousOn
  refine ⟨max R 0, le_max_right _ _, ?_⟩
  intro g hg
  refine ⟨e.symm (chart.symm g), ?_, (hR g hg).trans (le_max_left _ _)⟩
  change Exp (e (e.symm (chart.symm g))) = g
  rw [e.apply_symm_apply, ← hchart, chart.apply_symm_apply]

namespace CartanWordModel

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {H : LieSubalgebra ℝ L} [H.IsCartanSubalgebra] (M : CartanWordModel H)
  {n : ℕ} (T : TriangularAdjoint L n)
  (hunimod : ∀ x : L, LinearMap.trace ℝ L (ad ℝ L x) = 0)
  {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  (eW : HeightSpace T.character ≃ₗ[ℝ] W)
  {EN N : Type*} [NormedAddCommGroup EN] [NormedSpace ℝ EN]
  [FiniteDimensional ℝ EN] [TopologicalSpace N] [ChartedSpace EN N] [Group N]
  [LieGroup (𝓘(ℝ, EN)) ⊤ N] [T2Space N]
  (eN : cartanRootIdeal H ≃ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, EN)) N)
  (ExpN : GroupLieAlgebra (𝓘(ℝ, EN)) N → N) (hExpN : IsGroupExponential ExpN)
  (chartN : GroupLieAlgebra (𝓘(ℝ, EN)) N ≃ₜ N) (hchartN : ∀ x, chartN x = ExpN x)
  (dynkinN : NilpotentDynkinExpansionInput EN N)
  {ED D : Type*} [NormedAddCommGroup ED] [NormedSpace ℝ ED]
  [FiniteDimensional ℝ ED] [TopologicalSpace D] [ChartedSpace ED D] [Group D]
  [LieGroup (𝓘(ℝ, ED)) ⊤ D] [T2Space D]
  (eD : H ≃ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, ED)) D)
  (ExpD : GroupLieAlgebra (𝓘(ℝ, ED)) D → D) (hExpD : IsGroupExponential ExpD)
  (chartD : GroupLieAlgebra (𝓘(ℝ, ED)) D ≃ₜ D) (hchartD : ∀ x, chartD x = ExpD x)
  (dynkinD : NilpotentDynkinExpansionInput ED D)
  (φ : D →* MulAut N)

include hExpD dynkinD hchartN hchartD in
/-- Compact semidirect increments have the same polynomial endpoint bound.
The only path restriction is containment of their actual Cartan prefix heights. -/
theorem exists_compact_semidirect_word_bound
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    (γ : M.Bases) {K : Set (N × D)} (hK : IsCompact K)
    (hφ : ∀ d, φ d = M.adjointGroupAutomorphism T eN ExpN hExpN
      (by rw [← show chartN = ExpN from funext hchartN]; exact chartN.bijective) dynkinN
      (cartanLog H eD ExpD
        (by rw [← show chartD = ExpD from funext hchartD]; exact chartD.bijective) d)) :
    ∃ (C : ℝ) (q : ℕ), 0 ≤ C ∧ ∀ {E : Set W}, IsCompact E → E.Nonempty →
      ∀ β : M.Bases,
      IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList b₀)
        (M.boxCost T hunimod eW E) β.val →
      ∀ r : ℝ, 0 ≤ r → ∀ (m : ℕ) (u : ℕ → N) (v : ℕ → D),
      (∀ i < m, (u i, v i) ∈ K) →
      (∀ i < m, ∃ w ∈ E,
        eW (heightProjection T.character
          (cartanLog H eD ExpD
            (by rw [← show chartD = ExpD from funext hchartD]; exact chartD.bijective)
            (wordPrefix v i) : L)) = r • w) →
      (wordPrefix (fun i => (⟨u i, v i⟩ : N ⋊[φ] D)) m).left ∈
        M.groupBox T hunimod eW (ExpN ∘ eN) E β r (C * (1 + (m : ℝ)) ^ q) := by
  have hbijN : Function.Bijective ExpN := funext hchartN ▸ chartN.bijective
  have hbijD : Function.Bijective ExpD := funext hchartD ▸ chartD.bijective
  obtain ⟨RN, hRN, hN⟩ := exists_compact_exponential_coordinate_bound eN ExpN chartN hchartN
    (WordBasisSelections.basis M.letter M.wordList γ) (hK.image continuous_fst)
  obtain ⟨RD, hRD, hD⟩ := exists_compact_exponential_coordinate_bound eD ExpD chartD hchartD
    (finBasis ℝ H) (hK.image continuous_snd)
  obtain ⟨C, q, hC, hb⟩ := M.exists_semidirect_word_bound T hunimod eW eN ExpN hExpN
    hbijN dynkinN eD ExpD hExpD hbijD dynkinD φ b₀ hφ hRN hRD
  refine ⟨C, q, hC, ?_⟩
  intro E hE hne β hβ r hr m u v huv hh
  exact hb hE hne β hβ γ r hr m u v
    (fun i hi => hN ⟨(u i, v i), huv i hi, rfl⟩)
    (fun i hi => hD ⟨(u i, v i), huv i hi, rfl⟩) hh

end CartanWordModel
end PolycyclicRecognition

end

end OAI
