import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanStationaryPacking
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanPathPacking
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanSegmentExponent
import OAI.GroupTheory.PolycyclicRecognition.Algebra.TemplateThickeningLimit
import OAI.GroupTheory.PolycyclicRecognition.Analysis.PathVolumeComparison

namespace OAI

/-! # Actual stationary segment-volume comparison

The lower count uses independently sampled coordinates of the actual root
factor. The upper count uses the image paths in the ambient group. No
volume-comparison statement is assumed as an input.
-/

noncomputable section

namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule MeasureTheory Metric Set
open scoped Manifold NNReal ENNReal Pointwise

variable {EG G W : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [SimplyConnectedSpace G] [IsIsometricSMul G G]
  [ProperSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  [MeasurableSpace W] [BorelSpace W] [SecondCountableTopology W]
  {Λ : ℝ≥0} [MeasurableSpace (NormalizedPair G Λ)] [BorelSpace (NormalizedPair G Λ)]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H)
  {Exp : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H Exp)
  (hunimod : ∀ x : GroupLieAlgebra (𝓘(ℝ, EG)) G,
    LinearMap.trace ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G) (ad ℝ _ x) = 0)
  (eW : HeightSpace T.character ≃ₗ[ℝ] W) (π : G →* Multiplicative W)
  (hπExp : ∀ x, (π (Exp x)).toAdd = eW (heightProjection T.character x))
  (chartN : GroupLieAlgebra (𝓘(ℝ, F.N.modelSpace)) F.N.carrier ≃ₜ F.N.carrier)
  (hchartN : ∀ x, chartN x = F.ExpN x)
  (chartD : GroupLieAlgebra (𝓘(ℝ, F.D.modelSpace)) F.D.carrier ≃ₜ F.D.carrier)
  (hchartD : ∀ x, chartD x = F.ExpD x)
  (dynkinN : NilpotentDynkinExpansionInput F.N.modelSpace F.N.carrier)
  (dynkinD : NilpotentDynkinExpansionInput F.D.modelSpace F.D.carrier)
  (haarN : NilpotentExponentialHaarInput F.N.modelSpace F.N.carrier)
  (haarD : NilpotentExponentialHaarInput F.D.modelSpace F.D.carrier)

include hπExp hchartN hchartD dynkinN dynkinD haarN haarD in
/-- The stationary mean cannot decrease the segment-support norm on the
actual Cartan algebra. This is the geometric input to kernel factorization. -/
theorem segmentSupport_le_of_stationary_mean
    (hExp : IsGroupExponential Exp)
    (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
    (μ : Measure (NormalizedPair G Λ)) [IsProbabilityMeasure μ]
    (l : G →* Multiplicative W)
    (hπ : Continuous fun g => (π g).toAdd) (hl : Continuous fun g => (l g).toAdd)
    (hΛ : 0 < (Λ : ℝ)) {K L : ℝ} (hK : 0 ≤ K) (hL : 0 ≤ L)
    (hLip : ∀ x y, ‖(π x).toAdd - (π y).toAdd‖ ≤ K * dist x y)
    (hbound : ∀ g, ‖(l g).toAdd‖ ≤ L * dist 1 g)
    (hsub : ∀ ε : ℝ, 0 < ε → ∃ B : ℝ, 0 ≤ B ∧ ∀ g,
      ‖pairHeightL2 μ π hπ g - Lp.const 2 μ (l g).toAdd‖ ≤ ε * dist 1 g + B)
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    (hφ : ∀ d, F.action d = M.adjointGroupAutomorphism T F.N.equiv F.ExpN F.isExpN
      (by rw [← show chartN = F.ExpN from funext hchartN]; exact chartN.bijective) dynkinN
      (cartanLog H F.D.equiv F.ExpD
        (by rw [← show chartD = F.ExpD from funext hchartD]; exact chartD.bijective) d))
    (hpath : ∀ g : G, ∃ γ : ℝ → G, γ 0 = 1 ∧ γ 1 = g ∧
      ∀ t ∈ Icc (0 : ℝ) 1, ∀ u ∈ Icc (0 : ℝ) 1,
        dist (γ t) (γ u) ≤ dist 1 g * |t - u|)
    (v : H) :
    (M.supportIn T hunimod eW).segmentSupport (π (Exp v)).toAdd ≤
      (M.supportIn T hunimod eW).segmentSupport (l (Exp v)).toAdd := by
  classical
  obtain ⟨ε₀, C, Q, β, hε₀, hC, hQ, hβ, hlow⟩ :=
    M.exists_stationary_segment_separated_set T F hExp realize haarN dynkinN
      μ π l hπ hl hK hL hLip hbound hsub b₀ v (ρ := (Λ : ℝ) * ((Λ : ℝ) + 1))
      (mul_pos hΛ (by linarith))
  let d := |(columnBasisMatrix (wordListCoordinates M.letter M.wordList b₀) β.val).det|
  let V := Fin (finrank ℝ (cartanRootIdeal H)) → ℝ
  let a : ℝ≥0∞ := ENNReal.ofReal d * volume (ball (0 : V) ε₀) * (1 / 2)
  have hd : 0 < d := abs_pos.mpr (wordBasis_det_ne_zero M.letter M.wordList b₀ β)
  have hvol : 0 < volume (ball (0 : V) ε₀) := measure_ball_pos volume _ hε₀
  have hvolfin : volume (ball (0 : V) ε₀) < ⊤ :=
    lt_of_le_of_lt (measure_mono ball_subset_closedBall) (isCompact_closedBall (0 : V) ε₀).measure_lt_top
  have ha : 0 < a := pos_iff_ne_zero.mpr
    (mul_ne_zero (mul_ne_zero (ENNReal.ofReal_pos.mpr hd).ne' hvol.ne') (by norm_num))
  have hafin : a < ⊤ := by
    dsimp [a]
    exact ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hvolfin) (by norm_num)
  obtain ⟨D, k, hD, hupper⟩ := M.exists_coarse_path_polynomial_packing T F hunimod eW
    π hπExp chartN hchartN chartD hchartD dynkinN dynkinD haarN haarD b₀ β
    (show (0 : ℝ) < 1 by norm_num) hφ hpath hK hLip
  have hexp := M.maximizing_segment_exponent T hunimod eW b₀ v β hβ
  rw [← hπExp] at hexp
  have hE : IsCompact (segment ℝ (0 : W) (l (Exp v)).toAdd) := by
    rw [segment_eq_image]
    exact isCompact_Icc.image ((continuous_const.sub continuous_id).smul continuous_const |>.add
      (continuous_id.smul continuous_const))
  have hne : (segment ℝ (0 : W) (l (Exp v)).toAdd).Nonempty :=
    ⟨0, left_mem_segment ℝ _ _⟩
  apply le_of_eq_of_le hexp.symm
  rw [← SupportDatum.templateSupport_segment]
  apply (M.supportIn T hunimod eW).le_templateSupport_of_thickenings
    hE hne
  apply exponent_le_of_stationary_path_counts π _ _ hΛ hK hC ha hafin hQ hD k
  · intro δ hδ η hη
    obtain ⟨r₀, hr₀, hh⟩ := hlow δ hδ η hη
    refine ⟨r₀, hr₀, ?_⟩
    intro r hr
    obtain ⟨f, s, hsep, hmass, hpaths⟩ := hh r hr
    refine ⟨f, s, hsep, ?_, hpaths⟩
    convert hmass using 1; dsimp only [a, d, V]; ac_rfl
  · exact hupper hE hne

end PolycyclicRecognition.CartanWordModel

end

end OAI
