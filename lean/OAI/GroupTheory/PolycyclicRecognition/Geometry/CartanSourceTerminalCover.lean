import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanPathPacking
import OAI.GroupTheory.PolycyclicRecognition.Analysis.SequencePathCover
import OAI.GroupTheory.PolycyclicRecognition.Analysis.NormalizedPairPacking
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanFactorHaarInvariance

namespace OAI

/-! # Source terminal covers transported through the normalized quasi-isometry -/

noncomputable section

namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule MeasureTheory Metric Set Filter
open scoped Manifold ENNReal NNReal Pointwise Topology

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
theorem exists_normalized_source_terminal_cover
    [SimplyConnectedSpace G] [ProperSpace G]
    (hExpG : IsGroupExponential ExpG)
    (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    (γ₀ : M.Bases)
    (hpath : ∀ g : G, ∃ γ : ℝ → G, γ 0 = 1 ∧ γ 1 = g ∧
      ∀ t ∈ Icc (0 : ℝ) 1, ∀ u ∈ Icc (0 : ℝ) 1,
        dist (γ t) (γ u) ≤ dist 1 g * |t - u|)
    {Kπ : ℝ≥0} (hπ : LipschitzWith Kπ (fun g => (π g).toAdd))
    {E : Set W} (hE : IsCompact E) (hne : E.Nonempty)
    (scale : ℕ → ℝ) (hs : Tendsto scale atTop atTop)
    (S : ℕ → Set G) (hS : ∀ n, TotallyBounded (S n))
    {C b : ℝ} (hC : 0 ≤ C)
    (hpaths : ∀ η : ℝ, 0 < η → ∀ᶠ n in atTop, ∀ x ∈ S n,
      ∃ γ : Path (1 : G) x,
        PathMetricBound γ (C * scale n) (C * (1 + Real.log (2 + scale n))) ∧
        ∀ t, ∃ z ∈ E, ‖(π (γ t)).toAdd - scale n • z‖ ≤
          η * scale n + b * (1 + Real.log (2 + scale n)))
    {Λ : ℝ≥0} (p : ℕ → NormalizedPair G Λ) (base : ℕ → G) :
    ∃ t : ℕ → Finset G,
      (∀ n, ∀ x ∈ S n, ∃ y ∈ t n, dist ((p n).val.1 (base n * x)) y ≤ Λ) ∧
      ∀ ε : ℝ, 0 < ε → HasSubexponentialUpperBoundSeq scale
        (fun n => ((t n).card : ℝ) / Real.exp (scale n *
          (M.supportIn T hunimod eW).templateSupport (E + closedBall 0 ε))) := by
  classical
  let : IsTopologicalGroup G := topologicalGroup_of_lieGroup (𝓘(ℝ, EG)) ⊤
  have hbijN : Function.Bijective F.ExpN := funext hchartN ▸ chartN.bijective
  have hbijD : Function.Bijective F.ExpD := funext hchartD ▸ chartD.bijective
  obtain ⟨D, k, hD, hupper⟩ := M.exists_coarse_path_polynomial_packing T F hunimod eW π hπExp
    chartN hchartN chartD hchartD dynkinN dynkinD haarN haarD b₀ γ₀ zero_lt_one
    (fun d => cartan_action_eq_adjoint_of_published_realization T M F hExpG realize hbijN hbijD dynkinN d)
    hpath Kπ.coe_nonneg (fun x y => by simpa only [dist_eq_norm] using hπ.dist_le_mul x y)
  obtain ⟨u, _, hcover, hrate⟩ := exists_sequence_path_cover scale hs π E
    (M.supportIn T hunimod eW).templateSupport S hS hC hD k hpaths (hupper hE hne)
  let t := fun n => (u n).image (fun x => (p n).val.1 (base n * x))
  refine ⟨t, ?_, ?_⟩
  · intro n x hx
    obtain ⟨y, hy, hxy⟩ := hcover n x hx
    refine ⟨(p n).val.1 (base n * y), Finset.mem_image.mpr ⟨y, hy, rfl⟩, ?_⟩
    calc
      _ ≤ Λ * dist (base n * x) (base n * y) := (p n).property.1.1.dist_le_mul _ _
      _ = Λ * dist x y := by rw [dist_mul_left]
      _ ≤ Λ := by simpa only [mul_one] using mul_le_mul_of_nonneg_left hxy Λ.coe_nonneg
  · intro ε hε δ hδ
    filter_upwards [hrate ε hε δ hδ] with n hn
    apply le_trans _ hn
    apply div_le_div_of_nonneg_right _ (Real.exp_pos _).le
    exact_mod_cast Finset.card_image_le

end PolycyclicRecognition.CartanWordModel

end

end OAI
