import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanPathLifts
import OAI.GroupTheory.PolycyclicRecognition.Analysis.MetricFactorComparison

namespace OAI

/-! # Logarithmic factor bounds for short ambient bridges

Unit words and the actual Cartan factorization give logarithmic bounds
for every ambient element and its fixed compact right thickening. The
nilpotent factor grows exponentially in ambient distance; the Cartan
logarithm grows only polynomially.
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

include hunimod hπExp hchartN hchartD dynkinN dynkinD in
/-- One factor lift controls the entire right cell. The bounds use the
actual ambient metric and preserve the endpoint's canonical height. -/
theorem exists_metric_factor_thickening_bound
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    (γ₀ : M.Bases) {J : Type*} [Fintype J]
    (b : Basis J ℝ (cartanRootIdeal H)) {U : Set (F.N.carrier × F.D.carrier)} (hU : IsCompact U)
    (hφ : ∀ d, F.action d = M.adjointGroupAutomorphism T F.N.equiv F.ExpN F.isExpN
      (by rw [← show chartN = F.ExpN from funext hchartN]; exact chartN.bijective) dynkinN
      (cartanLog H F.D.equiv F.ExpD
        (by rw [← show chartD = F.ExpD from funext hchartD]; exact chartD.bijective) d))
    (hpath : ∀ g : G, ∃ γ : ℝ → G, γ 0 = 1 ∧ γ 1 = g ∧
      ∀ t ∈ Icc (0 : ℝ) 1, ∀ u ∈ Icc (0 : ℝ) 1,
        dist (γ t) (γ u) ≤ dist 1 g * |t - u|)
    {K : ℝ} (hK : 0 ≤ K)
    (hLip : ∀ x y, ‖(π x).toAdd - (π y).toAdd‖ ≤ K * dist x y) :
    ∃ (CN CD A : ℝ) (p c : ℕ), 0 ≤ CN ∧ 0 ≤ CD ∧ 0 ≤ A ∧
      ∀ g : G, ∃ (u : F.N.carrier) (d : F.D.carrier),
        F.inclusionN u * F.inclusionD d = g ∧
        (π (F.inclusionD d)).toAdd = (π g).toAdd ∧
        ∀ z ∈ U,
          (∃ v : cartanRootIdeal H, F.ExpN (F.N.equiv v) = u * F.action d z.1 ∧
            ‖b.equivFun v‖ ≤ CN * (3 + dist 1 g) ^ p *
              Real.exp (A * (dist 1 g + 1))) ∧
          ‖(finBasis ℝ H).equivFun (cartanLog H F.D.equiv F.ExpD
            (by rw [← show chartD = F.ExpD from funext hchartD]; exact chartD.bijective)
            (d * z.2))‖ ≤ CD * (3 + dist 1 g) ^ c := by
  obtain ⟨C, CD, p, c, hC, hCD, hword⟩ := M.exists_ambient_word_thickening_bound
    T F hunimod eW π hπExp chartN hchartN chartD hchartD dynkinN dynkinD
    b₀ γ₀ (isCompact_closedBall (1 : G) 1) hU hφ
  obtain ⟨D, B, hD, hB, hcompare⟩ :=
    M.exists_height_ball_coordinate_bound T hunimod eW b₀ b
  refine ⟨D * C, CD, B * K, p, c,
    mul_nonneg hD hC, hCD, mul_nonneg hB hK, ?_⟩
  intro g
  obtain ⟨w, hw, hwg, hwlen⟩ := wordFactorization_of_minimizing_paths hpath g
  let u : ℕ → G := fun i => w.getD i 1
  let ρ := K * (dist 1 g + 1)
  have hρ : 0 ≤ ρ := mul_nonneg hK (by positivity)
  let E : Set W := ({0} : Set W) + closedBall 0 ρ
  have hE : IsCompact E := isCompact_singleton.add (isCompact_closedBall 0 ρ)
  have hEne : E.Nonempty := ⟨0 + 0, add_mem_add (mem_singleton 0) (by simpa using hρ)⟩
  obtain ⟨β, hβ, _⟩ := M.exists_maximizing_box_basis T hunimod eW b₀ E
  have hheight : ∀ i ≤ w.length, ∃ x ∈ E, (π (wordPrefix u i)).toAdd = (1 : ℝ) • x := by
    intro i _
    have hd : dist (1 : G) (wordPrefix u i) ≤ dist 1 g + 1 := by
      rw [wordPrefix_getD]
      have hlen : ((w.take i).length : ℝ) ≤ w.length := by
        exact_mod_cast List.length_take_le' i w
      exact (dist_one_list_prod_le_length (w.take i)
        (fun x hx => hw x (List.mem_of_mem_take hx))).trans
          (hlen.trans hwlen)
    have hπbound : ‖(π (wordPrefix u i)).toAdd‖ ≤ ρ := by
      have hh := hLip (wordPrefix u i) 1
      simp only [map_one, toAdd_one, sub_zero, dist_comm (wordPrefix u i)] at hh
      exact hh.trans (mul_le_mul_of_nonneg_left hd hK)
    refine ⟨(π (wordPrefix u i)).toAdd, ?_, by simp⟩
    simpa only [zero_add] using add_mem_add (mem_singleton (0 : W))
      (show (π (wordPrefix u i)).toAdd ∈ closedBall (0 : W) ρ from by
        simpa only [mem_closedBall, dist_zero_right] using hπbound)
  obtain ⟨n, d, hnd, hthick⟩ := hword hE hEne β hβ 1 zero_le_one w.length u
    (fun i _ => getD_mem_closedBall_one w hw i) hheight
  have he : wordPrefix u w.length = g := by
    rw [wordPrefix_getD, List.take_length, hwg]
  have hndg : F.inclusionN n * F.inclusionD d = g := hnd.trans he
  have hheightD : (π (F.inclusionD d)).toAdd = (π g).toAdd := by
    rw [← hndg, map_mul,
      F.inclusionN_height_eq_one T eW π hπExp
        (by rw [← show chartN = F.ExpN from funext hchartN]; exact chartN.bijective), one_mul]
  refine ⟨n, d, hndg, hheightD, ?_⟩
  intro z hz
  obtain ⟨hN, hCartan⟩ := hthick z hz
  have hsize : 2 + (w.length : ℝ) ≤ 3 + dist 1 g := by linarith
  constructor
  · obtain ⟨v, hv, hnorm⟩ := hN
    refine ⟨v, hv, ?_⟩
    have hc := hcompare ρ hρ β v
    have hnorm' := hnorm.trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hsize p) hC)
    calc
      _ ≤ D * Real.exp (B * ρ) * (C * (3 + dist 1 g) ^ p) :=
        hc.trans (mul_le_mul_of_nonneg_left hnorm' (mul_nonneg hD (Real.exp_nonneg _)))
      _ = _ := by
        rw [show B * ρ = B * K * (dist 1 g + 1) by dsimp [ρ]; ring]
        ring
  · exact hCartan.trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hsize c) hCD)

end PolycyclicRecognition.CartanWordModel

end

end OAI
