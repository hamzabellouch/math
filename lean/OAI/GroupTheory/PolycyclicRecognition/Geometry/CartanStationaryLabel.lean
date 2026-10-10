import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanStationaryFactor
import OAI.GroupTheory.PolycyclicRecognition.Analysis.PairMeasureScaling
import OAI.GroupTheory.PolycyclicRecognition.Analysis.PairSublinear
import OAI.GroupTheory.PolycyclicRecognition.Analysis.SupportSymmetries

namespace OAI

/-! # Finite labels from forward and inverse stationary volume comparison -/

noncomputable section

namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule MeasureTheory Metric Set
open scoped Manifold NNReal ENNReal Pointwise

variable {EG G W : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [SimplyConnectedSpace G] [IsIsometricSMul G G]
  [ProperSpace G] [SecondCountableTopology G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
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

include hunimod hπExp hchartN hchartD dynkinN dynkinD haarN haarD in
/-- Forward volume comparison and the actual coupled inverse force the
stationary mean into the finite support-symmetry group. -/
theorem exists_finite_label_of_stationary_mean
    (hExp : IsGroupExponential Exp)
    (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
    (m : Measure G) [m.IsHaarMeasure] [m.IsMulRightInvariant]
    (μ : Measure (NormalizedPair G Λ)) [IsProbabilityMeasure μ]
    [SMulInvariantMeasure G (NormalizedPair G Λ) μ]
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
    (ψ : ℕ → NormalizedPair G Λ → W)
    (hψ : ∀ n, MemLp (ψ n) 2 μ) (hψm : ∀ n, Measurable (ψ n))
    (happrox : ∀ Q : Set G, IsCompact Q →
      Filter.Tendsto (fun n => ⨆ t ∈ Q,
        ∫⁻ p, ‖pairTransferDefect π l (ψ n) t p‖ₑ ^ 2 ∂μ) Filter.atTop (nhds 0)) :
    ∃ A : supportSymmetryGroup (M.supportIn T hunimod eW),
      ∀ g, (l g).toAdd = A.val (π g).toAdd := by
  obtain ⟨A₀, hA₀⟩ := M.exists_invertible_height_factor_of_stationary_mean
    T F hunimod eW π hπExp chartN hchartN chartD hchartD dynkinN dynkinD haarN haarD
    hExp realize μ l hπ hl hΛ hK hL hLip hbound hsub b₀ hφ hpath
  let A := A₀.toContinuousLinearEquiv
  let l' : G →* Multiplicative W := A.symm.toLinearMap.toAddMonoidHom.toMultiplicative.comp π
  have hA (g : G) : (l g).toAdd = A (π g).toAdd := hA₀ g
  obtain ⟨ν, hν, hν0, hνinv, hνsub⟩ :=
    inverseCoupling_sublinear m μ A π l hπ hl hA ψ hψ hψm happrox hpath
  let := hν
  let := hνinv
  obtain ⟨σ, hσ, hσinv, hσsub⟩ :=
    exists_probability_with_same_pairHeight_slope ν hν0 π l' hπ hνsub
  let := hσ
  have hl' : Continuous fun g => (l' g).toAdd := A.symm.continuous.comp hπ
  have hbound' (g : G) : ‖(l' g).toAdd‖ ≤ ‖A.symm.toContinuousLinearMap‖ * K * dist 1 g := by
    have hπg : ‖(π g).toAdd‖ ≤ K * dist 1 g := by
      simpa only [map_one, toAdd_one, sub_zero, dist_comm] using hLip g 1
    calc
      _ ≤ ‖A.symm.toContinuousLinearMap‖ * ‖(π g).toAdd‖ :=
        A.symm.toContinuousLinearMap.le_opNorm _
      _ ≤ ‖A.symm.toContinuousLinearMap‖ * (K * dist 1 g) :=
        mul_le_mul_of_nonneg_left hπg (norm_nonneg _)
      _ = _ := by ring
  have hsurj : ∀ w : W, ∃ v : H, (π (Exp v)).toAdd = w := by
    intro w
    obtain ⟨v, hv⟩ := (eW.surjective.comp (cartan_height_surjective T H)) w
    exact ⟨v, (hπExp v).trans hv⟩
  have hfwd (w : W) : (M.supportIn T hunimod eW).segmentSupport w ≤
      (M.supportIn T hunimod eW).segmentSupport (A w) := by
    obtain ⟨v, rfl⟩ := hsurj w
    simpa only [hA] using M.segmentSupport_le_of_stationary_mean
      T F hunimod eW π hπExp chartN hchartN chartD hchartD dynkinN dynkinD haarN haarD
      hExp realize μ l hπ hl hΛ hK hL hLip hbound hsub b₀ hφ hpath v
  have hinv (w : W) : (M.supportIn T hunimod eW).segmentSupport w ≤
      (M.supportIn T hunimod eW).segmentSupport (A.symm w) := by
    obtain ⟨v, rfl⟩ := hsurj w
    exact M.segmentSupport_le_of_stationary_mean
      T F hunimod eW π hπExp chartN hchartN chartD hchartD dynkinN dynkinD haarN haarD
      hExp realize σ l' hπ hl' hΛ hK (mul_nonneg (norm_nonneg _) hK) hLip hbound'
      hσsub b₀ hφ hpath v
  have hiso : A ∈ supportSymmetryGroup (M.supportIn T hunimod eW) :=
    support_preserved_of_forward_inverse (M.supportIn T hunimod eW) A.toLinearEquiv hfwd hinv
  exact ⟨⟨A, hiso⟩, hA⟩

end PolycyclicRecognition.CartanWordModel

end

end OAI
