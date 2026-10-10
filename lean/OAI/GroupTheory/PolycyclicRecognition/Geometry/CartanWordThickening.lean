import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanAmbientWords
import OAI.GroupTheory.PolycyclicRecognition.Algebra.WordExtension

namespace OAI

/-! # Thickening a fixed lift of an ambient word

The same lift works for every bounded right increment. This is stronger than
choosing an unrelated bounded lift at each endpoint, and is the input needed
for product-measure packing when the Cartan factors overlap.
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
/-- A fixed lift of each controlled ambient word has its entire bounded
right thickening inside one product of polynomially enlarged boxes. -/
theorem exists_ambient_word_thickening_bound
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    (γ : M.Bases) {K : Set G} (hK : IsCompact K)
    {U : Set (F.N.carrier × F.D.carrier)} (hU : IsCompact U)
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
      (∀ i ≤ m, ∃ w ∈ E, (π (wordPrefix u i)).toAdd = r • w) →
      ∃ (n : F.N.carrier) (d : F.D.carrier),
        F.inclusionN n * F.inclusionD d = wordPrefix u m ∧
        ∀ z ∈ U,
          n * F.action d z.1 ∈ M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv) E β r
            (C * (2 + (m : ℝ)) ^ q) ∧
          ‖(finBasis ℝ H).equivFun (cartanLog H F.D.equiv F.ExpD
            (by rw [← show chartD = F.ExpD from funext hchartD]; exact chartD.bijective)
            (d * z.2))‖ ≤ A * (2 + (m : ℝ)) ^ c := by
  obtain ⟨K', hK', hlift⟩ := exists_compact_cartan_word_lifts F hK
  have hKU := hK'.union hU
  have hbijN : Function.Bijective F.ExpN := funext hchartN ▸ chartN.bijective
  have hbijD : Function.Bijective F.ExpD := funext hchartD ▸ chartD.bijective
  obtain ⟨C, q, hC, hbox⟩ := M.exists_compact_semidirect_word_bound T hunimod eW
    F.N.equiv F.ExpN F.isExpN chartN hchartN dynkinN
    F.D.equiv F.ExpD F.isExpD chartD hchartD dynkinD F.action b₀ γ hKU hφ
  obtain ⟨RD, hRD, hD⟩ := exists_compact_exponential_coordinate_bound
    F.D.equiv F.ExpD chartD hchartD (finBasis ℝ H) (hKU.image continuous_snd)
  obtain ⟨A, c, hA, hlog⟩ := exists_cartan_word_log_bound H F.D.equiv F.ExpD
    hbijD F.isExpD dynkinD hRD
  refine ⟨C, A, q, c, hC, hA, ?_⟩
  intro E hE hne β hβ r hr m u hu hh
  obtain ⟨v, w, hvw, hprefix⟩ := hlift u m hu
  let n := (wordPrefix (fun i => (⟨v i, w i⟩ :
    F.N.carrier ⋊[F.action] F.D.carrier)) m).left
  let d := wordPrefix w m
  refine ⟨n, d, hprefix m le_rfl, ?_⟩
  intro z hz
  let v' := extendWord v m z.1
  let w' := extendWord w m z.2
  have hinc (i : ℕ) (hi : i < m + 1) : (v' i, w' i) ∈ K' ∪ U := by
    by_cases him : i < m
    · exact Or.inl (by simpa only [v', w', extendWord_before v m z.1 him,
        extendWord_before w m z.2 him] using hvw i him)
    · have he : i = m := by omega
      subst i
      exact Or.inr (by simpa only [v', w', extendWord_at] using hz)
  have hheight (i : ℕ) (hi : i < m + 1) : ∃ a ∈ E,
      eW (heightProjection T.character
        (cartanLog H F.D.equiv F.ExpD hbijD (wordPrefix w' i) :
          GroupLieAlgebra (𝓘(ℝ, EG)) G)) = r • a := by
    have him : i ≤ m := by omega
    obtain ⟨a, ha, he⟩ := hh i him
    rw [show wordPrefix w' i = wordPrefix w i from wordPrefix_extendWord w m z.2 him]
    exact ⟨a, ha, (F.lifted_prefix_height T eW π hπExp hbijN hbijD u v w i
      (hprefix i him)).trans he⟩
  have hleft : (wordPrefix (fun i => (⟨v' i, w' i⟩ :
      F.N.carrier ⋊[F.action] F.D.carrier)) (m + 1)).left = n * F.action d z.1 := by
    rw [wordPrefix_succ, SemidirectProduct.mul_left]
    have he : wordPrefix (fun i => (⟨v' i, w' i⟩ :
        F.N.carrier ⋊[F.action] F.D.carrier)) m =
        wordPrefix (fun i => (⟨v i, w i⟩ : F.N.carrier ⋊[F.action] F.D.carrier)) m := by
      apply wordPrefix_congr
      intro i hi
      simp only [v', w', extendWord_before v m z.1 hi, extendWord_before w m z.2 hi]
    rw [he, semidirect_wordPrefix_right]
    change n * F.action d (extendWord v m z.1 m) = n * F.action d z.1
    rw [extendWord_at]
  have hm : 1 + ((m + 1 : ℕ) : ℝ) = 2 + (m : ℝ) := by push_cast; ring
  constructor
  · have hb := hbox hE hne β hβ r hr (m + 1) v' w' hinc hheight
    rwa [hleft, hm] at hb
  · have hb := hlog w' (m + 1) (fun i hi => hD ⟨(v' i, w' i), hinc i hi, rfl⟩)
    rw [show wordPrefix w' (m + 1) = d * z.2 from wordPrefix_extendWord_succ w m z.2,
      hm] at hb
    exact hb

end PolycyclicRecognition.CartanWordModel

end

end OAI
