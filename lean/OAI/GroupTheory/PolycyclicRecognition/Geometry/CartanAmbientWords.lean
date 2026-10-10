import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanFactorHeight
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanCompactWords

namespace OAI

/-! # Upper boxes for actual ambient word paths

Compact factor lifts and exact height transfer connect the previously proved
semidirect estimates to words in the original Lie group. Neither a factor
word nor its prefix heights are supplied by the caller.
-/

noncomputable section

namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule
open scoped Manifold

variable {EG G : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G]
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

include hπExp hchartN hchartD dynkinN dynkinD in
/-- All ambient words whose actual prefix heights remain in `r E` have a
nilpotent coordinate in the same maximizing box with polynomial radius. -/
theorem exists_ambient_word_box_bound
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    (γ : M.Bases) {K : Set G} (hK : IsCompact K)
    (hφ : ∀ d, F.action d = M.adjointGroupAutomorphism T F.N.equiv F.ExpN F.isExpN
      (by rw [← show chartN = F.ExpN from funext hchartN]; exact chartN.bijective) dynkinN
      (cartanLog H F.D.equiv F.ExpD
        (by rw [← show chartD = F.ExpD from funext hchartD]; exact chartD.bijective) d)) :
    ∃ (C : ℝ) (q : ℕ), 0 ≤ C ∧ ∀ {E : Set W}, IsCompact E → E.Nonempty →
      ∀ β : M.Bases,
      IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList b₀)
        (M.boxCost T hunimod eW E) β.val →
      ∀ r : ℝ, 0 ≤ r → ∀ (m : ℕ) (u : ℕ → G),
      (∀ i < m, u i ∈ K) →
      (∀ i < m, ∃ w ∈ E, (π (wordPrefix u i)).toAdd = r • w) →
      ∃ (n : F.N.carrier) (d : F.D.carrier),
        F.inclusionN n * F.inclusionD d = wordPrefix u m ∧
        n ∈ M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv) E β r
          (C * (1 + (m : ℝ)) ^ q) := by
  obtain ⟨K', hK', hlift⟩ := exists_compact_cartan_word_lifts F hK
  have hbijN : Function.Bijective F.ExpN := funext hchartN ▸ chartN.bijective
  have hbijD : Function.Bijective F.ExpD := funext hchartD ▸ chartD.bijective
  obtain ⟨C, q, hC, hbound⟩ := M.exists_compact_semidirect_word_bound T hunimod eW
    F.N.equiv F.ExpN F.isExpN chartN hchartN dynkinN
    F.D.equiv F.ExpD F.isExpD chartD hchartD dynkinD F.action b₀ γ hK' hφ
  refine ⟨C, q, hC, ?_⟩
  intro E hE hne β hβ r hr m u hu hh
  obtain ⟨v, w, hvw, hprefix⟩ := hlift u m hu
  have hheight (i : ℕ) (hi : i < m) : ∃ z ∈ E,
      eW (heightProjection T.character
        (cartanLog H F.D.equiv F.ExpD hbijD (wordPrefix w i) :
          GroupLieAlgebra (𝓘(ℝ, EG)) G)) = r • z := by
    obtain ⟨z, hz, he⟩ := hh i hi
    exact ⟨z, hz, (F.lifted_prefix_height T eW π hπExp hbijN hbijD u v w i
      (hprefix i hi.le)).trans he⟩
  refine ⟨(wordPrefix (fun i => (⟨v i, w i⟩ :
    F.N.carrier ⋊[F.action] F.D.carrier)) m).left, wordPrefix w m, hprefix m le_rfl, ?_⟩
  exact hbound hE hne β hβ r hr m v w hvw hheight

include hπExp hchartN hchartD dynkinN dynkinD in
/-- Both factors of an ambient word admit bounds for the same lift: the
nilpotent coordinate lies in its weighted box and the Cartan logarithm has
polynomial size. Constants depend only on the compact increment set. -/
theorem exists_ambient_word_factor_bound
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    (γ : M.Bases) {K : Set G} (hK : IsCompact K)
    (hφ : ∀ d, F.action d = M.adjointGroupAutomorphism T F.N.equiv F.ExpN F.isExpN
      (by rw [← show chartN = F.ExpN from funext hchartN]; exact chartN.bijective) dynkinN
      (cartanLog H F.D.equiv F.ExpD
        (by rw [← show chartD = F.ExpD from funext hchartD]; exact chartD.bijective) d)) :
    ∃ (C A : ℝ) (q c : ℕ), 0 ≤ C ∧ 0 ≤ A ∧ ∀ {E : Set W}, IsCompact E → E.Nonempty →
      ∀ β : M.Bases,
      IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList b₀)
        (M.boxCost T hunimod eW E) β.val →
      ∀ r : ℝ, 0 ≤ r → ∀ (m : ℕ) (u : ℕ → G),
      (∀ i < m, u i ∈ K) →
      (∀ i < m, ∃ w ∈ E, (π (wordPrefix u i)).toAdd = r • w) →
      ∃ (n : F.N.carrier) (d : F.D.carrier),
        F.inclusionN n * F.inclusionD d = wordPrefix u m ∧
        n ∈ M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv) E β r
          (C * (1 + (m : ℝ)) ^ q) ∧
        ‖(finBasis ℝ H).equivFun (cartanLog H F.D.equiv F.ExpD
          (by rw [← show chartD = F.ExpD from funext hchartD]; exact chartD.bijective) d)‖ ≤
          A * (1 + (m : ℝ)) ^ c := by
  obtain ⟨K', hK', hlift⟩ := exists_compact_cartan_word_lifts F hK
  have hbijN : Function.Bijective F.ExpN := funext hchartN ▸ chartN.bijective
  have hbijD : Function.Bijective F.ExpD := funext hchartD ▸ chartD.bijective
  obtain ⟨C, q, hC, hbound⟩ := M.exists_compact_semidirect_word_bound T hunimod eW
    F.N.equiv F.ExpN F.isExpN chartN hchartN dynkinN
    F.D.equiv F.ExpD F.isExpD chartD hchartD dynkinD F.action b₀ γ hK' hφ
  obtain ⟨RD, hRD, hD⟩ := exists_compact_exponential_coordinate_bound
    F.D.equiv F.ExpD chartD hchartD (finBasis ℝ H) (hK'.image continuous_snd)
  obtain ⟨A, c, hA, hlog⟩ := exists_cartan_word_log_bound H F.D.equiv F.ExpD
    hbijD F.isExpD dynkinD hRD
  refine ⟨C, A, q, c, hC, hA, ?_⟩
  intro E hE hne β hβ r hr m u hu hh
  obtain ⟨v, w, hvw, hprefix⟩ := hlift u m hu
  have hheight (i : ℕ) (hi : i < m) : ∃ z ∈ E,
      eW (heightProjection T.character
        (cartanLog H F.D.equiv F.ExpD hbijD (wordPrefix w i) :
          GroupLieAlgebra (𝓘(ℝ, EG)) G)) = r • z := by
    obtain ⟨z, hz, he⟩ := hh i hi
    exact ⟨z, hz, (F.lifted_prefix_height T eW π hπExp hbijN hbijD u v w i
      (hprefix i hi.le)).trans he⟩
  refine ⟨(wordPrefix (fun i => (⟨v i, w i⟩ :
    F.N.carrier ⋊[F.action] F.D.carrier)) m).left, wordPrefix w m, hprefix m le_rfl, ?_⟩
  exact ⟨hbound hE hne β hβ r hr m v w hvw hheight,
    hlog w m (fun i hi => hD ⟨(v i, w i), hvw i hi, rfl⟩)⟩


end PolycyclicRecognition.CartanWordModel

end

end OAI
