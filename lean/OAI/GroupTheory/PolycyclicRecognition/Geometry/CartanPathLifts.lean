import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanWordThickening
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CoarsePathHeightWords

namespace OAI

/-! # Fixed factor lifts of height-controlled coarse paths

The chosen lift works for every bounded right increment simultaneously.
This is the form used for the two coordinate restrictions in tile counting.
-/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule Metric Set
open scoped Manifold Pointwise

variable {EG G : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [IsIsometricSMul G G] [ProperSpace G]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H)
  {ExpG : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H ExpG)
  (hunimod : ∀ x : GroupLieAlgebra (𝓘(ℝ, EG)) G,
    LinearMap.trace ℝ _ (ad ℝ _ x) = 0)
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
/-- Unit subdivision of an actual coarse path supplies a fixed factor
lift with polynomial coordinate bounds, including a prescribed compact
right thickening. All heights refer to the original homomorphism. -/
theorem exists_coarse_path_thickening_bound
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    (γ₀ : M.Bases) {U : Set (F.N.carrier × F.D.carrier)} (hU : IsCompact U)
    (hφ : ∀ d, F.action d = M.adjointGroupAutomorphism T F.N.equiv F.ExpN F.isExpN
      (by rw [← show chartN = F.ExpN from funext hchartN]; exact chartN.bijective) dynkinN
      (cartanLog H F.D.equiv F.ExpD
        (by rw [← show chartD = F.ExpD from funext hchartD]; exact chartD.bijective) d))
    (hpath : ∀ g : G, ∃ γ : ℝ → G, γ 0 = 1 ∧ γ 1 = g ∧
      ∀ t ∈ Icc (0 : ℝ) 1, ∀ u ∈ Icc (0 : ℝ) 1,
        dist (γ t) (γ u) ≤ dist 1 g * |t - u|)
    {K : ℝ} (hK : 0 ≤ K)
    (hLip : ∀ x y, ‖(π x).toAdd - (π y).toAdd‖ ≤ K * dist x y) :
    ∃ (C A : ℝ) (q c : ℕ), 0 ≤ C ∧ 0 ≤ A ∧
      ∀ {E : Set W}, IsCompact E → E.Nonempty →
      ∀ {r L κ B ε : ℝ}, 0 < r → 0 ≤ L → 0 ≤ κ → 0 ≤ ε →
      K * (κ + 2) + B ≤ r * ε → ∀ β : M.Bases,
      IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList b₀)
        (M.boxCost T hunimod eW (E + closedBall 0 ε)) β.val →
      ∀ {g : G} (γ : Path (1 : G) g), PathMetricBound γ L κ →
      (∀ t, ∃ z ∈ E, ‖(π (γ t)).toAdd - r • z‖ ≤ B) →
      ∃ (n : F.N.carrier) (d : F.D.carrier),
        F.inclusionN n * F.inclusionD d = g ∧
        (π (F.inclusionD d)).toAdd = (π g).toAdd ∧
        ∀ z ∈ U,
          n * F.action d z.1 ∈ M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv)
            (E + closedBall 0 ε) β r (C * (3 + (L + 1) * (κ + 2)) ^ q) ∧
          ‖(finBasis ℝ H).equivFun (cartanLog H F.D.equiv F.ExpD
            (by rw [← show chartD = F.ExpD from funext hchartD]; exact chartD.bijective)
            (d * z.2))‖ ≤ A * (3 + (L + 1) * (κ + 2)) ^ c := by
  obtain ⟨C, A, q, c, hC, hA, hthick⟩ := M.exists_ambient_word_thickening_bound
    T F hunimod eW π hπExp chartN hchartN chartD hchartD dynkinN dynkinD
    b₀ γ₀ (isCompact_closedBall (1 : G) 1) hU hφ
  refine ⟨C, A, q, c, hC, hA, ?_⟩
  intro E hE hne r L κ B ε hr hL hκ hε herr β hβ g γ hγ hh
  obtain ⟨w, hw, hp, hlen, hheight⟩ := exists_height_controlled_word_of_coarse_path
    hpath π hK hLip γ hL hκ hγ E r B hh
  let m := ⌈(L + 1) * (κ + 2)⌉₊
  have hm : (L + 1) * (κ + 2) ≤ (m : ℝ) := Nat.le_ceil _
  have hm' : (m : ℝ) < (L + 1) * (κ + 2) + 1 := Nat.ceil_lt_add_one (by positivity)
  have hwm : w.length ≤ m := by exact_mod_cast hlen.trans hm
  let u : ℕ → G := fun i => w.getD i 1
  have hu : ∀ i < m, u i ∈ closedBall (1 : G) 1 :=
    fun i _ => getD_mem_closedBall_one w hw i
  have he : wordPrefix u m = g := by
    rw [wordPrefix_getD, List.take_of_length_le hwm, hp]
  have hheight' : ∀ i ≤ m, ∃ z ∈ E + closedBall (0 : W) ε,
      (π (wordPrefix u i)).toAdd = r • z := by
    intro i _
    rw [wordPrefix_getD]
    obtain ⟨z, hz, hez⟩ := hheight i
    exact exists_scaled_thickening_of_norm_sub_smul_le hz hr (hez.trans herr)
  have hE' : IsCompact (E + closedBall (0 : W) ε) := hE.add (isCompact_closedBall 0 ε)
  have hne' : (E + closedBall (0 : W) ε).Nonempty := by
    obtain ⟨z, hz⟩ := hne
    exact ⟨z + 0, add_mem_add hz (by simpa using hε)⟩
  obtain ⟨n, d, hnd, hndU⟩ := hthick hE' hne' β hβ r hr.le m u hu hheight'
  have hnd' : F.inclusionN n * F.inclusionD d = g := hnd.trans he
  have hheightD : (π (F.inclusionD d)).toAdd = (π g).toAdd := by
    rw [← hnd', map_mul,
      F.inclusionN_height_eq_one T eW π hπExp
        (by rw [← show chartN = F.ExpN from funext hchartN]; exact chartN.bijective),
      one_mul]
  have hsize : 2 + (m : ℝ) ≤ 3 + (L + 1) * (κ + 2) := by linarith
  refine ⟨n, d, hnd', hheightD, ?_⟩
  intro z hz
  obtain ⟨hN, hD⟩ := hndU z hz
  constructor
  · obtain ⟨v, hv, hnorm⟩ := hN
    refine ⟨v, hv, hnorm.trans ?_⟩
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hsize q) hC
  · exact hD.trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (by positivity) hsize c) hA)

end PolycyclicRecognition.CartanWordModel

end

end OAI
