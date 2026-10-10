import OAI.GroupTheory.PolycyclicRecognition.Geometry.SequenceCartanPathLifts
import OAI.GroupTheory.PolycyclicRecognition.Analysis.SequenceConeQuotientBoxes
import OAI.GroupTheory.PolycyclicRecognition.Analysis.FactorProductPacking

namespace OAI

/-! # The first path gives a thickened quotient restriction

The fixed path lift and the zero-width projection are used for the same
endpoint and the same compact right cell. This keeps the later quotient
frame change independent of the nonunique factorization.
-/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule Metric Set Filter MeasureTheory
open scoped Manifold Pointwise Topology

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
/-- Controlled paths whose inside letter widths vanish yield a common
finite-volume quotient restriction after compact right thickening. -/
theorem exists_sequence_path_quotient_restriction
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
    (hLip : ∀ x y, ‖(π x).toAdd - (π y).toAdd‖ ≤ K * dist x y)
    {E : Set W} (hE : IsCompact E) (hne : E.Nonempty)
    (β : M.Bases)
    (hβ : IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList b₀)
      (M.boxCost T hunimod eW E) β.val)
    (scale L κ B ε : ℕ → ℝ) (hscale : Tendsto scale atTop atTop)
    (hscale0 : ∀ n, 0 < scale n) (hL0 : ∀ n, 0 ≤ L n) (hκ0 : ∀ n, 0 ≤ κ n)
    (hε0 : ∀ n, 0 ≤ ε n) (hε : Tendsto ε atTop (𝓝 0))
    (hL : HasSubexponentialUpperBoundSeq scale L)
    (hκ : HasSubexponentialUpperBoundSeq scale κ)
    (herr : ∀ n, K * (κ n + 2) + B n ≤ scale n * ε n)
    (C : Set (H →ₗ[ℝ] ℝ))
    (hzero : ∀ i, (M.weight i : H →ₗ[ℝ] ℝ) ∈ C →
      (M.supportIn T hunimod eW).weightSupport E i = 0)
    (Q : NilpotentLieModel ((cartanRootIdeal H) ⧸ M.coneWordIdeal C))
    (ExpQ : GroupLieAlgebra (𝓘(ℝ, Q.modelSpace)) Q.carrier → Q.carrier)
    (hExpQ : IsGroupExponential ExpQ)
    (haarQ : NilpotentExponentialHaarInput Q.modelSpace Q.carrier)
    (πQ : F.N.carrier →* Q.carrier)
    (hπQ : ∀ v, πQ (F.ExpN (F.N.equiv v)) = ExpQ (Q.equiv (M.coneProjection C v)))
    {k : ℕ} (bQ : Basis (Fin k) ℝ ((cartanRootIdeal H) ⧸ M.coneWordIdeal C))
    (μQ : Measure Q.carrier) [μQ.IsHaarMeasure]
    (α : F.D.carrier →* MulAut Q.carrier) (act : G →* Equiv.Perm Q.carrier)
    (hact : ∀ u d q, act (F.inclusionN u * F.inclusionD d) q = πQ u * α d q) :
    ∃ (RQ : ℕ → Set Q.carrier) (RD : ℕ → ℝ),
      (∀ n, μQ (RQ n) ≠ ⊤) ∧
      HasSubexponentialUpperBoundSeq scale (fun n => (μQ (RQ n)).toReal) ∧
      (∀ n, 0 ≤ RD n) ∧ HasSubexponentialUpperBoundSeq scale RD ∧
      ∀ n {g : G} (γ : Path (1 : G) g), PathMetricBound γ (L n) (κ n) →
        (∀ t, ∃ z ∈ E, ‖(π (γ t)).toAdd - scale n • z‖ ≤ B n) →
        ∃ (u : F.N.carrier) (d : F.D.carrier),
          F.inclusionN u * F.inclusionD d = g ∧
          (π (F.inclusionD d)).toAdd = (π g).toAdd ∧
          ∀ z ∈ U,
            act (g * (F.inclusionN z.1 * F.inclusionD z.2)) 1 ∈ RQ n ∧
            ‖(finBasis ℝ H).equivFun (cartanLog H F.D.equiv F.ExpD
              (by rw [← show chartD = F.ExpD from funext hchartD]; exact chartD.bijective)
              (d * z.2))‖ ≤ RD n := by
  obtain ⟨RN, RD, hRN0, hRD0, hRN, hRD, hlift⟩ := M.exists_sequence_coarse_path_lifts
    T F hunimod eW π hπExp chartN hchartN chartD hchartD dynkinN dynkinD
    b₀ γ₀ hU hφ hpath hK hLip hE hne β hβ
    scale L κ B ε hscale hscale0 hL0 hκ0 hε0 hε hL hκ herr
  obtain ⟨RQ, hfinite, hvol, hproject⟩ := M.exists_sequence_cone_quotient_envelope C
    (F.ExpN ∘ F.N.equiv) Q ExpQ hExpQ haarQ πQ hπQ bQ μQ
    scale RN hscale hRN0 hRN
  refine ⟨RQ, RD, hfinite, hvol, hRD0, hRD, ?_⟩
  intro n g γ hγ hh
  obtain ⟨u, d, hgd, hd, hthick⟩ := hlift n γ hγ hh
  refine ⟨u, d, hgd, hd, ?_⟩
  intro z hz
  refine ⟨?_, (hthick z hz).2⟩
  have heq : g * (F.inclusionN z.1 * F.inclusionD z.2) =
      F.inclusionN (u * F.action d z.1) * F.inclusionD (d * z.2) := by
    rw [← hgd]
    exact (factorTranslate_projection F.action F.inclusionN F.inclusionD F.conjugation
      (u, d) z).symm
  rw [heq, hact, map_one, mul_one]
  exact hproject n β ((M.supportIn T hunimod eW).weightSupport E) hzero
    ⟨u * F.action d z.1, (hthick z hz).1, rfl⟩

end PolycyclicRecognition.CartanWordModel

end

end OAI
