import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanWordPacking
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CoarsePathHeightWords

namespace OAI

/-! # Ambient packing for coarse paths with controlled heights

Unit-step subdivision increases the height error by only the logarithmic
coarse-path error. Its polynomial number of steps is absorbed by the
previously proved Cartan word-packing bound.
-/

noncomputable section

namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule MeasureTheory Metric Set
open scoped Manifold ENNReal Pointwise

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
/-- Coarse paths with a common speed and error have the expected separated
endpoint bound in a fixed enlargement of their height template. -/
theorem exists_coarse_path_polynomial_packing [ProperSpace G]
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    (γ₀ : M.Bases) {ρ : ℝ} (hρ : 0 < ρ)
    (hφ : ∀ d, F.action d = M.adjointGroupAutomorphism T F.N.equiv F.ExpN F.isExpN
      (by rw [← show chartN = F.ExpN from funext hchartN]; exact chartN.bijective) dynkinN
      (cartanLog H F.D.equiv F.ExpD
        (by rw [← show chartD = F.ExpD from funext hchartD]; exact chartD.bijective) d))
    (hpath : ∀ g : G, ∃ γ : ℝ → G, γ 0 = 1 ∧ γ 1 = g ∧
      ∀ t ∈ Icc (0 : ℝ) 1, ∀ u ∈ Icc (0 : ℝ) 1,
        dist (γ t) (γ u) ≤ dist 1 g * |t - u|)
    {K : ℝ} (hK : 0 ≤ K)
    (hLip : ∀ x y, ‖(π x).toAdd - (π y).toAdd‖ ≤ K * dist x y) :
    ∃ (D : ℝ) (k : ℕ), 0 < D ∧ ∀ {E : Set W}, IsCompact E → E.Nonempty →
      ∀ {r L κ B ε : ℝ}, 0 < r → 0 ≤ L → 0 ≤ κ → 0 ≤ ε →
      K * (κ + 2) + B ≤ r * ε → ∀ s : Finset G,
      (∀ x ∈ s, ∀ y ∈ s, x ≠ y → ρ ≤ dist x y) →
      (∀ x ∈ s, ∃ γ : Path (1 : G) x, PathMetricBound γ L κ ∧
        ∀ t, ∃ z ∈ E, ‖(π (γ t)).toAdd - r • z‖ ≤ B) →
      (s.card : ℝ) ≤ D * (3 + (L + 1) * (κ + 2)) ^ k *
        Real.exp (r * (M.supportIn T hunimod eW).templateSupport (E + closedBall 0 ε)) := by
  obtain ⟨D, k, hD, hcount⟩ := M.exists_ambient_word_polynomial_packing
    T F hunimod eW π hπExp chartN hchartN chartD hchartD dynkinN dynkinD
    haarN haarD b₀ γ₀ (isCompact_closedBall (1 : G) 1) hρ hφ
  refine ⟨D, k, hD, ?_⟩
  intro E hE hne r L κ B ε hr hL hκ hε herr s hsep hpaths
  let m := ⌈(L + 1) * (κ + 2)⌉₊
  have hm : (L + 1) * (κ + 2) ≤ (m : ℝ) := Nat.le_ceil _
  have hm' : (m : ℝ) < (L + 1) * (κ + 2) + 1 := Nat.ceil_lt_add_one (by positivity)
  have hEnlarge : IsCompact (E + closedBall (0 : W) ε) :=
    hE.add (isCompact_closedBall 0 ε)
  have hEnlargeNe : (E + closedBall (0 : W) ε).Nonempty := by
    obtain ⟨z, hz⟩ := hne
    exact ⟨z + 0, Set.add_mem_add hz (by simpa using hε)⟩
  have hend : ∀ x ∈ s, ∃ u : ℕ → G,
      (∀ i < m, u i ∈ closedBall (1 : G) 1) ∧
      (∀ i ≤ m, ∃ z ∈ E + closedBall (0 : W) ε, (π (wordPrefix u i)).toAdd = r • z) ∧
      wordPrefix u m = x := by
    intro x hx
    obtain ⟨γ, hγ, hh⟩ := hpaths x hx
    obtain ⟨w, hw, hp, hlen, hheight⟩ := exists_height_controlled_word_of_coarse_path
      hpath π hK hLip γ hL hκ hγ E r B hh
    have hwm : w.length ≤ m := by exact_mod_cast hlen.trans hm
    refine ⟨fun i => w.getD i 1, (fun i _ => getD_mem_closedBall_one w hw i), ?_, ?_⟩
    · intro i _
      rw [wordPrefix_getD]
      obtain ⟨z, hz, he⟩ := hheight i
      exact exists_scaled_thickening_of_norm_sub_smul_le hz hr (he.trans herr)
    · rw [wordPrefix_getD, List.take_of_length_le hwm, hp]
  have hc := hcount hEnlarge hEnlargeNe r hr.le m s hsep hend
  apply hc.trans
  apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
  apply mul_le_mul_of_nonneg_left _ hD.le
  apply pow_le_pow_left₀ (by positivity)
  linarith

end PolycyclicRecognition.CartanWordModel

end

end OAI
