import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanCocycleWords
import OAI.GroupTheory.PolycyclicRecognition.Analysis.CocycleCompactWords
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanAmbientWords
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanSamplingParameters

namespace OAI

/-! # Sublinear cocycles on compact words in the ambient Cartan group

The actual compact factor lifts control both factors of the same word. The
nilpotent factor lies in a polynomially enlarged root box; the Cartan factor
remains a word in one compact set, where nilpotent reduced cohomology applies.
-/

noncomputable section
namespace PolycyclicRecognition

open Module LieAlgebra LieModule Set
open scoped Manifold

variable {EG G : Type} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [SimplyConnectedSpace G]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  {ExpG : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H ExpG)
  (M : CartanWordModel H) (hExpG : IsGroupExponential ExpG)
  (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
  (haarN : NilpotentExponentialHaarInput F.N.modelSpace F.N.carrier)
  (dynkinN : NilpotentDynkinExpansionInput F.N.modelSpace F.N.carrier)
  (chartN : GroupLieAlgebra (𝓘(ℝ, F.N.modelSpace)) F.N.carrier ≃ₜ F.N.carrier)
  (hchartN : ∀ x, chartN x = F.ExpN x)
  (chartD : GroupLieAlgebra (𝓘(ℝ, F.D.modelSpace)) F.D.carrier ≃ₜ F.D.carrier)
  (hchartD : ∀ x, chartD x = F.ExpD x)
  (dynkinD : NilpotentDynkinExpansionInput F.D.modelSpace F.D.carrier)
  (hunimod : ∀ x : GroupLieAlgebra (𝓘(ℝ, EG)) G,
    LinearMap.trace ℝ _ (ad ℝ _ x) = 0)
  {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
  (eW : HeightSpace T.character ≃ₗ[ℝ] W) (π : G →* Multiplicative W)
  (hπExp : ∀ x, (π (ExpG x)).toAdd = eW (heightProjection T.character x))
  (hπcont : Continuous (fun g => (π g).toAdd))
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  (ρ : G →* (E ≃ₗᵢ[ℝ] E)) (hρ : ∀ v, Continuous (fun g => ρ g v))
  (hfix : ∀ v, (∀ g, ρ g v = v) → v = 0)

include T M hExpG realize haarN dynkinN hchartN hchartD dynkinD hunimod
  hπExp hπcont hρ hfix in
theorem cartan_cocycle_compact_words
    (b : G → E) (hbc : Continuous b) (hb : IsUnitaryCocycle ρ b)
    {K : Set G} (hK : IsCompact K) :
    ∀ ε : ℝ, 0 < ε → ∃ B : ℝ, 0 ≤ B ∧ ∀ (u : ℕ → G) (m : ℕ),
      (∀ i < m, u i ∈ K) → ‖b (wordPrefix u m)‖ ≤ ε * (m : ℝ) + B := by
  classical
  obtain ⟨K', hK', hlift⟩ := exists_compact_cartan_word_lifts F hK
  have hbijN : Function.Bijective F.ExpN := funext hchartN ▸ chartN.bijective
  have hbijD : Function.Bijective F.ExpD := funext hchartD ▸ chartD.bijective
  let b₀ := finBasis ℝ (cartanRootIdeal H)
  let γ : M.Bases := Classical.arbitrary _
  obtain ⟨C, q, hC, hbound⟩ := M.exists_compact_semidirect_word_bound T hunimod eW
    F.N.equiv F.ExpN F.isExpN chartN hchartN dynkinN
    F.D.equiv F.ExpD F.isExpD chartD hchartD dynkinD F.action b₀ γ hK'
    (fun d => cartan_action_eq_adjoint_of_published_realization T M F hExpG realize
      hbijN hbijD dynkinN d)
  let S := M.samplingPolytope T hunimod eW
  have hS : IsCompact S := M.isCompact_samplingPolytope T hunimod eW
  have hball : Metric.closedBall (0 : W) 1 ⊆ S :=
    closedBall_subset_weightSamplingPolytope _
  have hSne : S.Nonempty := ⟨0, hball (by simp)⟩
  obtain ⟨β, hβ⟩ := exists_maximizing_wordBasis M.letter M.wordList b₀
    (M.boxCost T hunimod eW S)
  obtain ⟨R, hR⟩ := hK.exists_bound_of_continuousOn hπcont.continuousOn
  let A := max R 1
  have hA : 1 ≤ A := le_max_right _ _
  have hApos : 0 < A := lt_of_lt_of_le zero_lt_one hA
  intro ε hε
  obtain ⟨B, hB, hN⟩ := cartan_cocycle_polynomial_boxes T F M hExpG realize haarN dynkinN
    ρ hρ hfix b hbc hb b₀ ((M.supportIn T hunimod eW).weightSupport S)
    (M.sampling_weightSupport_pos T hunimod eW) β hβ hC q
    (ε / (2 * A)) (div_pos hε (by positivity))
  obtain ⟨φ, hφ⟩ := cartan_cocycle_approximation T F M hExpG realize haarN dynkinN
    ρ hρ hfix b hbc hb (Prod.snd '' K') (hK'.image continuous_snd)
    (by positivity : 0 < ε / 2)
  refine ⟨B + 2 * ‖φ‖, by positivity, ?_⟩
  intro u m hu
  by_cases hm : m = 0
  · subst m
    simp only [wordPrefix_zero, hb.map_one, norm_zero, Nat.cast_zero, mul_zero, zero_add]
    positivity
  have hmpos : 0 < (m : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hm
  let r := A * (m : ℝ)
  have hr : 0 < r := mul_pos hApos hmpos
  obtain ⟨v, w, hvw, hprefix⟩ := hlift u m hu
  have hheight (i : ℕ) (hi : i < m) : ∃ z ∈ S,
      eW (heightProjection T.character
        (cartanLog H F.D.equiv F.ExpD hbijD (wordPrefix w i) :
          GroupLieAlgebra (𝓘(ℝ, EG)) G)) = r • z := by
    let z := r⁻¹ • (π (wordPrefix u i)).toAdd
    have hn : ‖(π (wordPrefix u i)).toAdd‖ ≤ r := by
      have h := norm_height_wordPrefix_le π u i (R := A)
        (fun j hj => (hR _ (hu j (hj.trans hi))).trans (le_max_left _ _))
      have him : (i : ℝ) ≤ m := by exact_mod_cast hi.le
      exact h.trans (by dsimp [r]; nlinarith)
    have hz : ‖z‖ ≤ 1 := by
      dsimp only [z]
      rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hr, ← div_eq_inv_mul]
      exact (div_le_one hr).2 hn
    refine ⟨z, hball (by simpa using hz), ?_⟩
    rw [F.lifted_prefix_height T eW π hπExp hbijN hbijD u v w i (hprefix i hi.le)]
    dsimp [z]
    rw [smul_smul, mul_inv_cancel₀ hr.ne', one_smul]
  have hbox := hbound hS hSne β hβ r hr.le m v w hvw hheight
  obtain ⟨x, hx, hxbound⟩ := hbox
  have hmle : (m : ℝ) ≤ r := by dsimp [r]; nlinarith
  have hxbound' : ‖(M.boxBasis T hunimod eW S β r).equivFun x‖ ≤ C * (1 + r) ^ q :=
    hxbound.trans (mul_le_mul_of_nonneg_left (by gcongr) hC)
  have hn := hN r hr.le x hxbound'
  change ‖b (F.inclusionN ((F.ExpN ∘ F.N.equiv) x))‖ ≤ _ at hn
  rw [hx] at hn
  have hd := hb.norm_mapped_wordPrefix_le_of_coboundary F.inclusionD
    (Prod.snd '' K') φ hφ w m (fun i hi => ⟨(v i, w i), hvw i hi, rfl⟩)
  have heq : (ε / (2 * A)) * r = (ε / 2) * (m : ℝ) := by
    dsimp [r]
    field_simp
  calc
    ‖b (wordPrefix u m)‖ = ‖b (F.inclusionN
        ((wordPrefix (fun i => (⟨v i, w i⟩ : F.N.carrier ⋊[F.action] F.D.carrier)) m).left) *
        F.inclusionD (wordPrefix w m))‖ := by rw [hprefix m le_rfl]
    _ ≤ _ := hb.norm_mul_le _ _
    _ ≤ ((ε / (2 * A)) * r + B) + ((m : ℝ) * (ε / 2) + 2 * ‖φ‖) := add_le_add hn hd
    _ = ε * (m : ℝ) + (B + 2 * ‖φ‖) := by rw [heq]; ring

include T M hExpG realize haarN dynkinN hchartN hchartD dynkinD hunimod
  hπExp hπcont hρ hfix in
theorem cartan_cocycle_sublinear
    (b : G → E) (hbc : Continuous b) (hb : IsUnitaryCocycle ρ b)
    {K : Set G} (hK : IsCompact K)
    (length : G → ℝ) (hlen : ∀ g, 0 ≤ length g) {c : ℝ} (hc : 0 ≤ c)
    (hword : ∀ g, ∃ l : List G, (∀ q ∈ l, q ∈ K) ∧ l.prod = g ∧
      (l.length : ℝ) ≤ c * length g + c) :
    ∀ ε : ℝ, 0 < ε → ∃ B : ℝ, 0 ≤ B ∧ ∀ g, ‖b g‖ ≤ ε * length g + B :=
  sublinear_of_compact_word_estimates b K
    (cartan_cocycle_compact_words T F M hExpG realize haarN dynkinN chartN hchartN
      chartD hchartD dynkinD hunimod eW π hπExp hπcont ρ hρ hfix b hbc hb hK)
    length hlen hc hword

end PolycyclicRecognition

end

end OAI
