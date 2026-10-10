import OAI.GroupTheory.PolycyclicRecognition.Analysis.SequenceMetricFactorBounds

namespace OAI

/-! # The short-bridge exponential constant precedes the scales -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule Metric Set Filter
open scoped Topology
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
theorem exists_uniform_sequence_metric_factor_bounds
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
    (hLip : ∀ x y, ‖(π x).toAdd - (π y).toAdd‖ ≤ K * dist x y)
    :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ (scale : ℕ → ℝ),
      Tendsto scale atTop atTop → (∀ n, 0 ≤ scale n) →
      ∃ RN RD : ℕ → ℝ, (∀ n, 0 ≤ RN n) ∧ (∀ n, 0 ≤ RD n) ∧
      HasSubexponentialUpperBoundSeq scale RN ∧ HasSubexponentialUpperBoundSeq scale RD ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ n (g : G), dist 1 g ≤ δ * scale n →
        ∃ (u : F.N.carrier) (d : F.D.carrier),
          F.inclusionN u * F.inclusionD d = g ∧
          (π (F.inclusionD d)).toAdd = (π g).toAdd ∧
          ∀ z ∈ U,
            (∃ v : cartanRootIdeal H, F.ExpN (F.N.equiv v) = u * F.action d z.1 ∧
              ‖b.equivFun v‖ ≤ RN n * Real.exp (A * δ * scale n)) ∧
            ‖(finBasis ℝ H).equivFun (cartanLog H F.D.equiv F.ExpD
              (by rw [← show chartD = F.ExpD from funext hchartD]; exact chartD.bijective)
              (d * z.2))‖ ≤ RD n := by
  obtain ⟨CN, CD, A, p, c, hCN, hCD, hA, hbound⟩ := M.exists_metric_factor_thickening_bound
    T F hunimod eW π hπExp chartN hchartN chartD hchartD dynkinN dynkinD
    b₀ γ₀ b hU hφ hpath hK hLip
  refine ⟨A, hA, ?_⟩
  intro scale hs hscale0
  let aN := (CN + 1) * Real.exp A * 3 ^ p
  let aD := (CD + 1) * 3 ^ c
  let RN := fun n => aN * (1 + scale n) ^ p
  let RD := fun n => aD * (1 + scale n) ^ c
  have haN : 0 < aN := by dsimp [aN]; positivity
  have haD : 0 < aD := by dsimp [aD]; positivity
  refine ⟨RN, RD, fun n => ?_, fun n => ?_,
    (subexponential_upper_polynomial haN p).along_sequence hs,
    (subexponential_upper_polynomial haD c).along_sequence hs, ?_⟩
  · exact mul_nonneg haN.le (pow_nonneg (by linarith [hscale0 n]) _)
  · exact mul_nonneg haD.le (pow_nonneg (by linarith [hscale0 n]) _)
  intro δ _ hδ n g hg
  have hdist : dist 1 g ≤ scale n := hg.trans
    (mul_le_of_le_one_left (hscale0 n) hδ)
  have hbase : 3 + dist 1 g ≤ 3 * (1 + scale n) := by linarith [hscale0 n]
  have hs1 : 0 ≤ 1 + scale n := by linarith [hscale0 n]
  obtain ⟨u, d, hgd, hd, hthick⟩ := hbound g
  refine ⟨u, d, hgd, hd, ?_⟩
  intro z hz
  obtain ⟨⟨v, hv, hNv⟩, hDv⟩ := hthick z hz
  constructor
  · refine ⟨v, hv, hNv.trans ?_⟩
    have hp : (3 + dist 1 g) ^ p ≤ (3 * (1 + scale n)) ^ p :=
      pow_le_pow_left₀ (by positivity) hbase p
    have he : Real.exp (A * (dist 1 g + 1)) ≤
        Real.exp A * Real.exp (A * δ * scale n) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      nlinarith [mul_le_mul_of_nonneg_left hg hA]
    calc
      _ ≤ CN * (3 * (1 + scale n)) ^ p *
          (Real.exp A * Real.exp (A * δ * scale n)) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hp hCN) he
          (Real.exp_nonneg _) (mul_nonneg hCN (pow_nonneg (mul_nonneg (by norm_num) hs1) _))
      _ ≤ RN n * Real.exp (A * δ * scale n) := by
        calc
          _ = CN * (Real.exp A * 3 ^ p * (1 + scale n) ^ p *
              Real.exp (A * δ * scale n)) := by rw [mul_pow]; ring
          _ ≤ (CN + 1) * (Real.exp A * 3 ^ p * (1 + scale n) ^ p *
              Real.exp (A * δ * scale n)) :=
            mul_le_mul_of_nonneg_right (by linarith) (by positivity)
          _ = _ := by dsimp [RN, aN]; ring
  · apply hDv.trans
    calc
      CD * (3 + dist 1 g) ^ c ≤ CD * (3 * (1 + scale n)) ^ c :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hbase c) hCD
      _ ≤ RD n := by
        rw [mul_pow]
        change CD * (3 ^ c * (1 + scale n) ^ c) ≤
          (CD + 1) * 3 ^ c * (1 + scale n) ^ c
        rw [mul_assoc (CD + 1)]
        exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)


end PolycyclicRecognition.CartanWordModel

end

end OAI
