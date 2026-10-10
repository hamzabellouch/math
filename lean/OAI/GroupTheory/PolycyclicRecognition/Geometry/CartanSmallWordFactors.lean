import OAI.GroupTheory.PolycyclicRecognition.Analysis.WordChartSmallProducts
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanFactorHeight
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanCompactWords

namespace OAI

/-! # Cartan word lifts with small rescaled Cartan coordinate -/

noncomputable section

namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule
open scoped Manifold

variable {EG G I : Type*} [Fintype I] [DecidableEq I] [NormedAddCommGroup EG] [NormedSpace ℝ EG]
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
/-- Keep the total size of the Cartan increments, in the same lift that
provides the nilpotent box bound. This is the small-chart estimate needed
when comparing nearby basepoints. -/
theorem exists_ambient_word_small_cartan_bound
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    (γ : M.Bases) {K : Set G} (hK : IsCompact K)
    (hφ : ∀ d, F.action d = M.adjointGroupAutomorphism T F.N.equiv F.ExpN F.isExpN
      (by rw [← show chartN = F.ExpN from funext hchartN]; exact chartN.bijective) dynkinN
      (cartanLog H F.D.equiv F.ExpD
        (by rw [← show chartD = F.ExpD from funext hchartD]; exact chartD.bijective) d))
    (X : I → H) {d : ℕ} (hDnil : lowerCentralSeries ℝ H H d = ⊥)
    (bD₀ : Basis (Fin (finrank ℝ H)) ℝ H)
    (βD : WordBasisSelections X (boundedBracketWords d))
    (hβD : IsMaximizingColumnBasis (wordListCoordinates X (boundedBracketWords d) bD₀)
      (fun w => bracketWordExponent (fun _ : I => 1) w) βD.val) :
    ∃ (C A R : ℝ) (q : ℕ), 0 ≤ C ∧ 0 ≤ A ∧ 0 ≤ R ∧
      ∀ {E : Set W}, IsCompact E → E.Nonempty → ∀ β : M.Bases,
      IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList b₀)
        (M.boxCost T hunimod eW E) β.val →
      ∀ r : ℝ, 0 ≤ r → ∀ s : ℝ, 1 ≤ s → ∀ (m : ℕ) (u : ℕ → G),
      (∀ i < m, u i ∈ K) →
      (∀ i < m, ∃ w ∈ E, (π (wordPrefix u i)).toAdd = r • w) →
      ∃ (n : F.N.carrier) (k : F.D.carrier),
        F.inclusionN n * F.inclusionD k = wordPrefix u m ∧
        n ∈ M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv) E β r
          (C * (1 + (m : ℝ)) ^ q) ∧
        ∃ z : H, F.ExpD (F.D.equiv z) = k ∧
          ‖(exponentialRescaleBasis (WordBasisSelections.basis X (boundedBracketWords d) βD)
            (fun j => bracketWordExponent (fun _ : I => 1) (βD.val j))
            (Real.log s)).equivFun z‖ ≤
              A * ((m : ℝ) * R / s) * (1 + (m : ℝ) * R / s) ^ d := by
  obtain ⟨K', hK', hlift⟩ := exists_compact_cartan_word_lifts F hK
  have hbijN : Function.Bijective F.ExpN := funext hchartN ▸ chartN.bijective
  have hbijD : Function.Bijective F.ExpD := funext hchartD ▸ chartD.bijective
  obtain ⟨C, q, hC, hbound⟩ := M.exists_compact_semidirect_word_bound T hunimod eW
    F.N.equiv F.ExpN F.isExpN chartN hchartN dynkinN
    F.D.equiv F.ExpD F.isExpD chartD hchartD dynkinD F.action b₀ γ hK' hφ
  obtain ⟨R, hR, hD⟩ := exists_compact_exponential_coordinate_bound
    F.D.equiv F.ExpD chartD hchartD
    (WordBasisSelections.basis X (boundedBracketWords d) βD) (hK'.image continuous_snd)
  obtain ⟨A, hA, hsmall⟩ := exists_word_chart_small_product_bound dynkinD F.D.equiv
    F.ExpD F.isExpD X hDnil bD₀ βD hβD
  refine ⟨C, A, R, q, hC, hA, hR, ?_⟩
  intro E hE hne β hβ r hr s hs m u hu hh
  obtain ⟨v, w, hvw, hprefix⟩ := hlift u m hu
  have hheight (i : ℕ) (hi : i < m) : ∃ z ∈ E,
      eW (heightProjection T.character
        (cartanLog H F.D.equiv F.ExpD hbijD (wordPrefix w i) :
          GroupLieAlgebra (𝓘(ℝ, EG)) G)) = r • z := by
    obtain ⟨z, hz, he⟩ := hh i hi
    exact ⟨z, hz, (F.lifted_prefix_height T eW π hπExp hbijN hbijD u v w i
      (hprefix i hi.le)).trans he⟩
  have hw (i : Fin m) : w i ∈ exponentialCoordinateBox (F.ExpD ∘ F.D.equiv)
      (WordBasisSelections.basis X (boundedBracketWords d) βD) R :=
    hD ⟨(v i, w i), hvw i i.isLt, rfl⟩
  choose Z hZ hZbound using hw
  obtain ⟨z, hz, hsmallz⟩ := hsmall s hs m Z R hR hZbound
  have hzprod : F.ExpD (F.D.equiv z) = wordPrefix w m := by
    rw [← hz]
    unfold wordPrefix
    apply congrArg List.prod
    apply congrArg List.ofFn
    funext i
    exact hZ i
  refine ⟨(wordPrefix (fun i => (⟨v i, w i⟩ :
    F.N.carrier ⋊[F.action] F.D.carrier)) m).left, wordPrefix w m,
    hprefix m le_rfl, ?_, z, hzprod, hsmallz⟩
  exact hbound hE hne β hβ r hr m v w hvw hheight

end PolycyclicRecognition.CartanWordModel

end

end OAI
