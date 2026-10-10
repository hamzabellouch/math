import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanSmallWordFactors
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanPathLifts
import OAI.GroupTheory.PolycyclicRecognition.Analysis.MetricFactorComparison

namespace OAI

/-! # A metric factor lift with small Cartan chart coordinates -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule Metric Set
open scoped Manifold Pointwise

variable {EG G I : Type*} [Fintype I] [DecidableEq I] [NormedAddCommGroup EG] [NormedSpace ℝ EG]
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
/-- The nilpotent factor has the usual exponential distance bound, while
the Cartan factor is small in the word chart whenever distance divided
by chart scale is small. Both bounds hold for the same factor lift. -/
theorem exists_small_metric_cartan_factor_bound
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    (γ₀ : M.Bases) {J : Type*} [Fintype J]
    (b : Basis J ℝ (cartanRootIdeal H))
    (hφ : ∀ d, F.action d = M.adjointGroupAutomorphism T F.N.equiv F.ExpN F.isExpN
      (by rw [← show chartN = F.ExpN from funext hchartN]; exact chartN.bijective) dynkinN
      (cartanLog H F.D.equiv F.ExpD
        (by rw [← show chartD = F.ExpD from funext hchartD]; exact chartD.bijective) d))
    (hpath : ∀ g : G, ∃ γ : ℝ → G, γ 0 = 1 ∧ γ 1 = g ∧
      ∀ t ∈ Icc (0 : ℝ) 1, ∀ u ∈ Icc (0 : ℝ) 1,
        dist (γ t) (γ u) ≤ dist 1 g * |t - u|)
    {K : ℝ} (hK : 0 ≤ K)
    (hLip : ∀ x y, ‖(π x).toAdd - (π y).toAdd‖ ≤ K * dist x y)
    (X : I → H) {d : ℕ} (hDnil : lowerCentralSeries ℝ H H d = ⊥)
    (bD₀ : Basis (Fin (finrank ℝ H)) ℝ H)
    (βD : WordBasisSelections X (boundedBracketWords d))
    (hβD : IsMaximizingColumnBasis (wordListCoordinates X (boundedBracketWords d) bD₀)
      (fun w => bracketWordExponent (fun _ : I => 1) w) βD.val) :
    ∃ (C A B R : ℝ) (q : ℕ), 0 ≤ C ∧ 0 ≤ A ∧ 0 ≤ B ∧ 0 ≤ R ∧
      ∀ s : ℝ, 1 ≤ s → ∀ g : G,
      ∃ (n : F.N.carrier) (k : F.D.carrier),
        F.inclusionN n * F.inclusionD k = g ∧
        (π (F.inclusionD k)).toAdd = (π g).toAdd ∧
        (∃ v : cartanRootIdeal H, F.ExpN (F.N.equiv v) = n ∧
          ‖b.equivFun v‖ ≤ C * (3 + dist 1 g) ^ q * Real.exp (A * (dist 1 g + 1))) ∧
        ∃ z : H, F.ExpD (F.D.equiv z) = k ∧
          ‖(exponentialRescaleBasis (WordBasisSelections.basis X (boundedBracketWords d) βD)
            (fun j => bracketWordExponent (fun _ : I => 1) (βD.val j))
            (Real.log s)).equivFun z‖ ≤
              B * ((dist 1 g + 1) * R / s) * (1 + (dist 1 g + 1) * R / s) ^ d := by
  obtain ⟨C, B, R, q, hC, hB, hR, hword⟩ := M.exists_ambient_word_small_cartan_bound
    T F hunimod eW π hπExp chartN hchartN chartD hchartD dynkinN dynkinD
    b₀ γ₀ (isCompact_closedBall (1 : G) 1) hφ X hDnil bD₀ βD hβD
  obtain ⟨D, A, hD, hA, hcompare⟩ := M.exists_height_ball_coordinate_bound
    T hunimod eW b₀ b
  refine ⟨D * C, A * K, B, R, q, mul_nonneg hD hC, mul_nonneg hA hK, hB, hR, ?_⟩
  intro s hs g
  obtain ⟨w, hw, hwg, hwlen⟩ := wordFactorization_of_minimizing_paths hpath g
  let u : ℕ → G := fun i => w.getD i 1
  let ρ := K * (dist 1 g + 1)
  let E : Set W := ({0} : Set W) + closedBall 0 ρ
  have hρ : 0 ≤ ρ := mul_nonneg hK (by positivity)
  have hE : IsCompact E := isCompact_singleton.add (isCompact_closedBall 0 ρ)
  have hEne : E.Nonempty := ⟨0 + 0, add_mem_add (mem_singleton 0) (by simpa using hρ)⟩
  obtain ⟨β, hβ, _⟩ := M.exists_maximizing_box_basis T hunimod eW b₀ E
  have hheight : ∀ i < w.length, ∃ x ∈ E, (π (wordPrefix u i)).toAdd = (1 : ℝ) • x := by
    intro i _
    have hd : dist (1 : G) (wordPrefix u i) ≤ dist 1 g + 1 := by
      rw [wordPrefix_getD]
      have hlen : ((w.take i).length : ℝ) ≤ w.length := by
        exact_mod_cast List.length_take_le' i w
      exact (dist_one_list_prod_le_length (w.take i)
        (fun x hx => hw x (List.mem_of_mem_take hx))).trans (hlen.trans hwlen)
    have hp : ‖(π (wordPrefix u i)).toAdd‖ ≤ ρ := by
      have hh := hLip (wordPrefix u i) 1
      simp only [map_one, toAdd_one, sub_zero, dist_comm (wordPrefix u i)] at hh
      exact hh.trans (mul_le_mul_of_nonneg_left hd hK)
    refine ⟨(π (wordPrefix u i)).toAdd, ?_, by simp⟩
    simpa only [zero_add] using add_mem_add (mem_singleton (0 : W))
      (show (π (wordPrefix u i)).toAdd ∈ closedBall (0 : W) ρ from by
        simpa only [mem_closedBall, dist_zero_right] using hp)
  obtain ⟨n, k, hnk, hn, z, hz, hzbound⟩ := hword hE hEne β hβ 1 zero_le_one s hs
    w.length u (fun i _ => getD_mem_closedBall_one w hw i) hheight
  have he : wordPrefix u w.length = g := by rw [wordPrefix_getD, List.take_length, hwg]
  have hfactor : F.inclusionN n * F.inclusionD k = g := hnk.trans he
  have hh : (π (F.inclusionD k)).toAdd = (π g).toAdd := by
    rw [← hfactor, map_mul, F.inclusionN_height_eq_one T eW π hπExp
      (by rw [← show chartN = F.ExpN from funext hchartN]; exact chartN.bijective), one_mul]
  refine ⟨n, k, hfactor, hh, ?_, z, hz, hzbound.trans ?_⟩
  · obtain ⟨v, hv, hnorm⟩ := hn
    refine ⟨v, hv, ?_⟩
    have hsize : 1 + (w.length : ℝ) ≤ 3 + dist 1 g := by linarith
    have hc := hcompare ρ hρ β v
    have hn' := hnorm.trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hsize q) hC)
    calc
      _ ≤ D * Real.exp (A * ρ) * (C * (3 + dist 1 g) ^ q) :=
        hc.trans (mul_le_mul_of_nonneg_left hn' (mul_nonneg hD (Real.exp_nonneg _)))
      _ = _ := by
        rw [show A * ρ = A * K * (dist 1 g + 1) by dsimp [ρ]; ring]
        ring
  · gcongr

end PolycyclicRecognition.CartanWordModel

end

end OAI
