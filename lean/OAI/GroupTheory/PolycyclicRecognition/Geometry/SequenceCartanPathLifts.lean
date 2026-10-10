import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanPathLifts
import OAI.GroupTheory.PolycyclicRecognition.Analysis.TemplateBoxEnvelopes
import OAI.GroupTheory.PolycyclicRecognition.Analysis.ControlledPathErrorEnvelope

namespace OAI

/-! # Common factor boxes for families of controlled paths

Vanishing height errors are absorbed in one fixed maximizing basis. The
endpoint and its compact right thickening share the same chosen factor lift.
-/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule Metric Set Filter
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
/-- One common subexponential pair of radii works for every path in the
family, including all its prescribed bounded right thickenings. -/
theorem exists_sequence_coarse_path_lifts
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
    (herr : ∀ n, K * (κ n + 2) + B n ≤ scale n * ε n) :
    ∃ RN RD : ℕ → ℝ, (∀ n, 0 ≤ RN n) ∧ (∀ n, 0 ≤ RD n) ∧
      HasSubexponentialUpperBoundSeq scale RN ∧ HasSubexponentialUpperBoundSeq scale RD ∧
      ∀ n {g : G} (γ : Path (1 : G) g), PathMetricBound γ (L n) (κ n) →
        (∀ t, ∃ z ∈ E, ‖(π (γ t)).toAdd - scale n • z‖ ≤ B n) →
        ∃ (u : F.N.carrier) (d : F.D.carrier),
          F.inclusionN u * F.inclusionD d = g ∧
          (π (F.inclusionD d)).toAdd = (π g).toAdd ∧
          ∀ z ∈ U,
            u * F.action d z.1 ∈ M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv)
              E β (scale n) (RN n) ∧
            ‖(finBasis ℝ H).equivFun (cartanLog H F.D.equiv F.ExpD
              (by rw [← show chartD = F.ExpD from funext hchartD]; exact chartD.bijective)
              (d * z.2))‖ ≤ RD n := by
  obtain ⟨C, A, q, c, hC, hA, hlift⟩ := M.exists_coarse_path_thickening_bound
    T F hunimod eW π hπExp chartN hchartN chartD hchartD dynkinN dynkinD
    b₀ γ₀ hU hφ hpath hK hLip
  let size := fun n => 3 + (L n + 1) * (κ n + 2)
  have hsize0 : ∀ n, 0 ≤ size n := fun n => by
    have hnL := hL0 n
    have hnκ := hκ0 n
    dsimp [size]
    positivity
  have hsize : HasSubexponentialUpperBoundSeq scale size :=
    (sequence_subexponential_upper_const hscale 3).add
      ((hL.add (sequence_subexponential_upper_const hscale 1) hscale).mul
        (hκ.add (sequence_subexponential_upper_const hscale 2) hscale)
        (Eventually.of_forall (fun n => add_nonneg (hL0 n) zero_le_one))) hscale
  let R := fun n => C * size n ^ q
  let RD := fun n => A * size n ^ c
  have hR0 : ∀ n, 0 ≤ R n := fun n => mul_nonneg hC (pow_nonneg (hsize0 n) _)
  have hRD0 : ∀ n, 0 ≤ RD n := fun n => mul_nonneg hA (pow_nonneg (hsize0 n) _)
  have hR : HasSubexponentialUpperBoundSeq scale R :=
    (sequence_subexponential_upper_const hscale C).mul
      (hsize.pow hscale (Eventually.of_forall hsize0) q) (Eventually.of_forall (fun _ => hC))
  have hRD : HasSubexponentialUpperBoundSeq scale RD :=
    (sequence_subexponential_upper_const hscale A).mul
      (hsize.pow hscale (Eventually.of_forall hsize0) c) (Eventually.of_forall (fun _ => hA))
  obtain ⟨RN, hRN0, hRN, henclose⟩ := M.exists_template_box_envelope_sequence T hunimod eW
    (F.ExpN ∘ F.N.equiv) b₀ hE hne β hβ scale ε R hscale (fun n => (hscale0 n).le)
      hε0 hε hR0 hR
  refine ⟨RN, RD, hRN0, hRD0, hRN, hRD, ?_⟩
  intro n g γ hγ hh
  obtain ⟨βn, hβn, _⟩ := M.exists_maximizing_box_basis T hunimod eW b₀
    (E + closedBall 0 (ε n))
  obtain ⟨u, d, hgd, hd, hthick⟩ := hlift hE hne (hscale0 n) (hL0 n) (hκ0 n)
    (hε0 n) (herr n) βn hβn γ hγ hh
  refine ⟨u, d, hgd, hd, ?_⟩
  intro z hz
  exact ⟨henclose n βn (hthick z hz).1, (hthick z hz).2⟩

include hπExp hchartN hchartD dynkinN dynkinD in
/-- The linear/logarithmic bounds of the selected-profile paths give common
subexponential factor boxes. The vanishing thickening tolerance is proved
from those bounds, rather than assumed for the family of paths. -/
theorem exists_sequence_controlled_profile_lifts
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
    (scale η : ℕ → ℝ) (hscale : Tendsto scale atTop atTop)
    (hscale1 : ∀ n, 1 ≤ scale n) (hη0 : ∀ n, 0 ≤ η n)
    (hη : Tendsto η atTop (𝓝 0))
    (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) :
    ∃ RN RD : ℕ → ℝ, (∀ n, 0 ≤ RN n) ∧ (∀ n, 0 ≤ RD n) ∧
      HasSubexponentialUpperBoundSeq scale RN ∧ HasSubexponentialUpperBoundSeq scale RD ∧
      ∀ n {g : G} (γ : Path (1 : G) g),
        PathMetricBound γ (A * scale n) (B * (1 + Real.log (2 + scale n))) →
        (∀ t, ∃ z ∈ E, ‖(π (γ t)).toAdd - scale n • z‖ ≤
          2 * scale n * η n + A * (1 + Real.log (2 + scale n))) →
        ∃ (u : F.N.carrier) (d : F.D.carrier),
          F.inclusionN u * F.inclusionD d = g ∧
          (π (F.inclusionD d)).toAdd = (π g).toAdd ∧
          ∀ z ∈ U,
            u * F.action d z.1 ∈ M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv)
              E β (scale n) (RN n) ∧
            ‖(finBasis ℝ H).equivFun (cartanLog H F.D.equiv F.ExpD
              (by rw [← show chartD = F.ExpD from funext hchartD]; exact chartD.bijective)
              (d * z.2))‖ ≤ RD n := by
  obtain ⟨ε, hε0, hε, hL, hκ, herr⟩ := exists_controlled_path_error_envelope
    scale η hscale hscale1 hη0 hη A B K hA hB hK
  exact M.exists_sequence_coarse_path_lifts T F hunimod eW π hπExp
    chartN hchartN chartD hchartD dynkinN dynkinD b₀ γ₀ hU hφ hpath hK hLip
    hE hne β hβ scale (fun n => A * scale n)
    (fun n => B * (1 + Real.log (2 + scale n)))
    (fun n => 2 * scale n * η n + A * (1 + Real.log (2 + scale n))) ε
    hscale (fun n => lt_of_lt_of_le zero_lt_one (hscale1 n))
    (fun n => mul_nonneg hA (zero_le_one.trans (hscale1 n)))
    (fun n => mul_nonneg hB (by
      have hl := Real.log_nonneg (show 1 ≤ 2 + scale n by linarith [hscale1 n])
      linarith)) hε0 hε hL hκ herr

end PolycyclicRecognition.CartanWordModel

end

end OAI
