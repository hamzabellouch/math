import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanWordThickening
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanHaarConjugation
import OAI.GroupTheory.PolycyclicRecognition.Analysis.FactorProductPacking
import OAI.GroupTheory.PolycyclicRecognition.Analysis.PositiveProjectionCell
import OAI.GroupTheory.PolycyclicRecognition.Analysis.ModelCubeHaar
import OAI.GroupTheory.PolycyclicRecognition.Analysis.PolynomialPackingAlgebra

namespace OAI

/-! # Ambient packing for controlled Cartan word endpoints

A positive cell in the product of the actual factors is translated by fixed
word lifts. These cells are disjoint after testing their projections in the
ambient metric. The word-thickening theorem encloses them in one product of
boxes, with the exact support exponential and polynomial radii.
-/

noncomputable section

namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule MeasureTheory Metric Set
open scoped Manifold ENNReal

variable {EG G : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [IsIsometricSMul G G]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H)
  {ExpG : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H ExpG)
  (hunimod : ∀ x : GroupLieAlgebra (𝓘(ℝ, EG)) G,
    LinearMap.trace ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G) (ad ℝ _ x) = 0)
  {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  (eW : HeightSpace T.character ≃ₗ[ℝ] W) (π : G →* Multiplicative W)
  (hπExp : ∀ x, (π (ExpG x)).toAdd = eW (heightProjection T.character x))
  (chartN : GroupLieAlgebra (𝓘(ℝ, F.N.modelSpace)) F.N.carrier ≃ₜ F.N.carrier)
  (hchartN : ∀ x, chartN x = F.ExpN x)
  (chartD : GroupLieAlgebra (𝓘(ℝ, F.D.modelSpace)) F.D.carrier ≃ₜ F.D.carrier)
  (hchartD : ∀ x, chartD x = F.ExpD x)
  (dynkinN : NilpotentDynkinExpansionInput F.N.modelSpace F.N.carrier)
  (dynkinD : NilpotentDynkinExpansionInput F.D.modelSpace F.D.carrier)
  (haarN : NilpotentExponentialHaarInput F.N.modelSpace F.N.carrier)
  (haarD : NilpotentExponentialHaarInput F.D.modelSpace F.D.carrier)

include hπExp hchartN hchartD dynkinN dynkinD haarN haarD in
/-- An ambient separated set of controlled word endpoints satisfies the
support-exponential volume bound. The source cell has positive finite mass;
all remaining dependence on word length is polynomial. -/
theorem exists_ambient_word_packing_bound
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    (γ : M.Bases) {K : Set G} (hK : IsCompact K) {ρ : ℝ} (hρ : 0 < ρ)
    (hφ : ∀ d, F.action d = M.adjointGroupAutomorphism T F.N.equiv F.ExpN F.isExpN
      (by rw [← show chartN = F.ExpN from funext hchartN]; exact chartN.bijective) dynkinN
      (cartanLog H F.D.equiv F.ExpD
        (by rw [← show chartD = F.ExpD from funext hchartD]; exact chartD.bijective) d)) :
    ∃ (Q : ℝ≥0∞) (B C A : ℝ) (q c : ℕ), 0 < Q ∧ Q < ⊤ ∧
      0 < B ∧ 0 ≤ C ∧ 0 ≤ A ∧ ∀ {E : Set W}, IsCompact E → E.Nonempty →
      ∀ r : ℝ, 0 ≤ r → ∀ (m : ℕ) (s : Finset G),
      (∀ x ∈ s, ∀ y ∈ s, x ≠ y → ρ ≤ dist x y) →
      (∀ x ∈ s, ∃ u : ℕ → G, (∀ i < m, u i ∈ K) ∧
        (∀ i ≤ m, ∃ w ∈ E, (π (wordPrefix u i)).toAdd = r • w) ∧ wordPrefix u m = x) →
      (s.card : ℝ≥0∞) * Q ≤
        ENNReal.ofReal B * ENNReal.ofReal
          (Real.exp (r * (M.supportIn T hunimod eW).templateSupport E)) *
        ENNReal.ofReal (2 * (C * (2 + (m : ℝ)) ^ q)) ^ finrank ℝ (cartanRootIdeal H) *
        ENNReal.ofReal (2 * (A * (2 + (m : ℝ)) ^ c)) ^ finrank ℝ H := by
  classical
  let : IsTopologicalGroup G := topologicalGroup_of_lieGroup (𝓘(ℝ, EG)) ⊤
  let : IsTopologicalGroup F.N.carrier := topologicalGroup_of_lieGroup (𝓘(ℝ, F.N.modelSpace)) ⊤
  let : IsTopologicalGroup F.D.carrier := topologicalGroup_of_lieGroup (𝓘(ℝ, F.D.modelSpace)) ⊤
  let cN := chartN.symm.trans
    (finBasis ℝ (GroupLieAlgebra (𝓘(ℝ, F.N.modelSpace)) F.N.carrier)).equivFun.toContinuousLinearEquiv.toHomeomorph
  let cD := chartD.symm.trans
    (finBasis ℝ (GroupLieAlgebra (𝓘(ℝ, F.D.modelSpace)) F.D.carrier)).equivFun.toContinuousLinearEquiv.toHomeomorph
  let : LocallyCompactSpace F.N.carrier := cN.locallyCompactSpace_iff.mpr inferInstance
  let : LocallyCompactSpace F.D.carrier := cD.locallyCompactSpace_iff.mpr inferInstance
  let : SecondCountableTopology F.N.carrier := cN.secondCountableTopology
  let : SecondCountableTopology F.D.carrier := cD.secondCountableTopology
  have hbijN : Function.Bijective F.ExpN := funext hchartN ▸ chartN.bijective
  have hbijD : Function.Bijective F.ExpD := funext hchartD ▸ chartD.bijective
  obtain ⟨μ, _, B, hμ, _, hB, hinv, hvol⟩ := M.exists_haar_adjoint_invariant_box_bounds
    T hunimod F.N.equiv F.ExpN F.isExpN hbijN dynkinN haarN eW b₀
  obtain ⟨ν, hν, hvolD⟩ := exists_model_haar_cube_volume F.D.equiv haarD F.ExpD F.isExpD
    inferInstance (finBasis ℝ H)
  let : μ.IsHaarMeasure := hμ
  let : ν.IsHaarMeasure := hν
  have hpres (d : F.D.carrier) : MeasurePreserving (F.action d) μ μ := by
    rw [hφ]
    exact hinv _
  let projection : F.N.carrier × F.D.carrier → G :=
    fun z => F.inclusionN z.1 * F.inclusionD z.2
  have hpcont : Continuous projection :=
    (F.closedN.continuous.comp continuous_fst).mul (F.closedD.continuous.comp continuous_snd)
  obtain ⟨U, hU, hUm, hUpos, hUfin, hsmall⟩ := exists_compact_positive_projection_cell
    (μ.prod ν) projection hpcont (1, 1) (half_pos hρ)
  have hsmall' (z) (hz : z ∈ U) : dist (1 : G) (projection z) < ρ / 2 := by
    simpa only [projection, map_one, one_mul] using hsmall z hz
  obtain ⟨C, A, q, c, hC, hA, hthick⟩ := M.exists_ambient_word_thickening_bound
    T F hunimod eW π hπExp chartN hchartN chartD hchartD dynkinN dynkinD b₀ γ hK hU hφ
  refine ⟨(μ.prod ν) U, B, C, A, q, c, hUpos, hUfin, hB, hC, hA, ?_⟩
  intro E hE hne r hr m s hsep hend
  obtain ⟨β, hβ, _⟩ := M.exists_maximizing_box_basis T hunimod eW b₀ E
  let BN := M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv) E β r (C * (2 + (m : ℝ)) ^ q)
  let BD := exponentialCoordinateBox (F.ExpD ∘ F.D.equiv) (finBasis ℝ H)
    (A * (2 + (m : ℝ)) ^ c)
  have hlifts : ∀ x ∈ s, ∃ p : F.N.carrier × F.D.carrier,
      projection p = x ∧ ∀ z ∈ U, factorTranslate F.action p z ∈ BN ×ˢ BD := by
    intro x hx
    obtain ⟨u, hu, hh, he⟩ := hend x hx
    obtain ⟨n, d, hnd, hb⟩ := hthick hE hne β hβ r hr m u hu hh
    refine ⟨(n, d), hnd.trans he, ?_⟩
    intro z hz
    obtain ⟨hn, hd⟩ := hb z hz
    refine ⟨hn, ?_⟩
    exact ⟨cartanLog H F.D.equiv F.ExpD hbijD (d * z.2),
      exp_cartanLog H F.D.equiv F.ExpD hbijD (d * z.2), hd⟩
  choose! p hp hpt using hlifts
  have hcount := factor_separated_card_mul_le F.action F.inclusionN F.inclusionD
    F.conjugation μ ν hpres s p U (BN ×ˢ BD) hUm hp hsmall' hsep
      (by rintro x hx z ⟨u, hu, rfl⟩; exact hpt x hx u hu)
  apply hcount.trans
  rw [Measure.prod_prod]
  apply mul_le_mul'
  · exact (hvol E β hβ r (C * (2 + (m : ℝ)) ^ q) (by positivity)).2
  · exact (hvolD (A * (2 + (m : ℝ)) ^ c) (by positivity)).le

include hπExp hchartN hchartD dynkinN dynkinD haarN haarD in
/-- The ambient word endpoint count has a uniform polynomial prefactor
and the exact Cartan support exponential. -/
theorem exists_ambient_word_polynomial_packing
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    (γ : M.Bases) {K : Set G} (hK : IsCompact K) {ρ : ℝ} (hρ : 0 < ρ)
    (hφ : ∀ d, F.action d = M.adjointGroupAutomorphism T F.N.equiv F.ExpN F.isExpN
      (by rw [← show chartN = F.ExpN from funext hchartN]; exact chartN.bijective) dynkinN
      (cartanLog H F.D.equiv F.ExpD
        (by rw [← show chartD = F.ExpD from funext hchartD]; exact chartD.bijective) d)) :
    ∃ (D : ℝ) (k : ℕ), 0 < D ∧ ∀ {E : Set W}, IsCompact E → E.Nonempty →
      ∀ r : ℝ, 0 ≤ r → ∀ (m : ℕ) (s : Finset G),
      (∀ x ∈ s, ∀ y ∈ s, x ≠ y → ρ ≤ dist x y) →
      (∀ x ∈ s, ∃ u : ℕ → G, (∀ i < m, u i ∈ K) ∧
        (∀ i ≤ m, ∃ w ∈ E, (π (wordPrefix u i)).toAdd = r • w) ∧ wordPrefix u m = x) →
      (s.card : ℝ) ≤ D * (2 + (m : ℝ)) ^ k *
        Real.exp (r * (M.supportIn T hunimod eW).templateSupport E) := by
  obtain ⟨Q, B, C, A, q, c, hQ, hQfin, hB, hC, hA, hcount⟩ :=
    M.exists_ambient_word_packing_bound T F hunimod eW π hπExp chartN hchartN
      chartD hchartD dynkinN dynkinD haarN haarD b₀ γ hK hρ hφ
  obtain ⟨D, hD, hpoly⟩ := exists_real_card_bound_of_box_factors hQ hQfin hB.le hC hA
    q c (finrank ℝ (cartanRootIdeal H)) (finrank ℝ H)
  refine ⟨D, q * finrank ℝ (cartanRootIdeal H) + c * finrank ℝ H, hD, ?_⟩
  intro E hE hne r hr m s hsep hend
  exact hpoly s (by positivity) (hcount hE hne r hr m s hsep hend)

end PolycyclicRecognition.CartanWordModel

end

end OAI
