import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanPathPacking
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanHaarConjugation
import OAI.GroupTheory.PolycyclicRecognition.Analysis.FixedSliceVolumeComparison
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CanonicalExponentialMeasure
import OAI.GroupTheory.PolycyclicRecognition.Algebra.TemplateThickeningLimit

namespace OAI

/-! # The volume comparison for compact accessible Cartan endpoint sets -/

noncomputable section

namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule MeasureTheory Filter Set
open scoped Manifold NNReal ENNReal

variable {EG G W : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [IsIsometricSMul G G] [ProperSpace G] [IsTopologicalGroup G]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  {Λ : ℝ≥0} {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H)
  {Exp : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H Exp)
  (hunimod : ∀ x : GroupLieAlgebra (𝓘(ℝ, EG)) G, LinearMap.trace ℝ _ (ad ℝ _ x) = 0)
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

include hπExp dynkinD haarN haarD in
/-- A compact successful logarithmic image of subexponential volume cannot
have a larger source support exponent than its image-path height template. -/
theorem accessible_templateSupport_le
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    (source target : Set W) (htarget : IsCompact target) (hne : target.Nonempty)
    (β : M.Bases)
    (hβ : IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList b₀)
      (M.boxCost T hunimod eW source) β.val)
    (C : ℝ → Set (Fin (finrank ℝ (cartanRootIdeal H)) → ℝ))
    (hC : ∀ r, IsCompact (C r))
    (hvol : HasSubexponentialLowerBound (fun r => (volume (C r)).toReal))
    (x : ℝ → G) (d : ℝ → F.D.carrier) (start : ℝ → G)
    (f : ℝ → NormalizedPair G Λ) (hΛ : 0 < (Λ : ℝ))
    (hφ : ∀ d, F.action d = M.adjointGroupAutomorphism T F.N.equiv F.ExpN F.isExpN
      (by rw [← show chartN = F.ExpN from funext hchartN]; exact chartN.bijective) dynkinN
      (cartanLog H F.D.equiv F.ExpD
        (by rw [← show chartD = F.ExpD from funext hchartD]; exact chartD.bijective) d))
    (hpath : ∀ g : G, ∃ γ : ℝ → G, γ 0 = 1 ∧ γ 1 = g ∧
      ∀ t ∈ Icc (0 : ℝ) 1, ∀ u ∈ Icc (0 : ℝ) 1,
        dist (γ t) (γ u) ≤ dist 1 g * |t - u|)
    {K L : ℝ} (hK : 0 ≤ K) (hL : 0 ≤ L)
    (hLip : ∀ g h, ‖(π g).toAdd - (π h).toAdd‖ ≤ K * dist g h)
    (hpaths : ∀ η : ℝ, 0 < η → ∀ᶠ r in atTop, ∀ y ∈ C r,
      ∃ γ : Path (start r)
        (x r * F.inclusionN (F.ExpN (F.N.equiv
          ((M.boxBasis T hunimod eW source β r).equivFun.symm y))) * F.inclusionD (d r)),
        PathMetricBound γ (L * r) (L * (1 + Real.log (2 + r))) ∧
        ∀ t, ∃ z ∈ target,
          ‖(π ((f r).val.1 (γ t))).toAdd - (π ((f r).val.1 (start r))).toAdd - r • z‖ ≤
            η * r + K * Λ * L * (1 + Real.log (2 + r))) :
    (M.supportIn T hunimod eW).templateSupport source ≤
      (M.supportIn T hunimod eW).templateSupport target := by
  let : IsTopologicalGroup F.N.carrier := topologicalGroup_of_lieGroup (𝓘(ℝ, F.N.modelSpace)) ⊤
  let μ := Measure.map ((F.ExpN ∘ F.N.equiv) ∘ b₀.equivFun.symm) volume
  have hnil : LieRing.IsNilpotent (cartanRootIdeal H) :=
    (LieModule.isNilpotent_iff ℝ _ _).mpr ⟨M.bound, M.bound_zero⟩
  let : μ.IsHaarMeasure := exponential_basis_measure_isHaar haarN F.N.equiv hnil F.ExpN F.isExpN b₀
  have hpres (d : F.D.carrier) : MeasurePreserving (F.action d) μ μ := by
    rw [hφ]
    exact exponentialConjugate_measurePreserving F.N.equiv F.ExpN
      (by rw [← show chartN = F.ExpN from funext hchartN]; exact chartN.bijective)
      chartN hchartN b₀ _ (M.det_idealAdjointAutomorphism_eq_one T hunimod _)
  let S := fun r => ((F.ExpN ∘ F.N.equiv) ∘
    (M.boxBasis T hunimod eW source β r).equivFun.symm) '' C r
  have hS (r : ℝ) : IsCompact (S r) :=
    (hC r).image (continuous_exponential_basis F.N.equiv F.ExpN chartN hchartN _)
  have hexp := M.columnBasisWeight_eq_templateSupport_of_maximizing T hunimod eW b₀ source β hβ
  have hmass : HasSubexponentialLowerBound (fun r =>
      (μ (S r)).toReal / Real.exp (r * (M.supportIn T hunimod eW).templateSupport source)) := by
    have hh := rescaled_image_volume_lower F.N.equiv F.ExpN chartN hchartN M.letter M.wordList
      b₀ β (M.boxCost T hunimod eW source) C hvol
    simpa only [μ, S, boxBasis, hexp] using hh
  obtain ⟨A, k, hA, hupper⟩ := M.exists_coarse_path_polynomial_packing T F hunimod eW π hπExp
    chartN hchartN chartD hchartD dynkinN dynkinD haarN haarD b₀ β
    (show (0 : ℝ) < 1 by norm_num) hφ hpath hK hLip
  apply (M.supportIn T hunimod eW).le_templateSupport_of_thickenings htarget hne
  apply fixedSlice_volume_exponent_le F.inclusionN F.inclusionD F.action μ hpres
    F.conjugation F.closedN S hS x d start f π target
    (M.supportIn T hunimod eW).templateSupport hΛ hK hL hmass
  · intro η hη
    filter_upwards [hpaths η hη] with r hr u hu
    obtain ⟨y, hy, rfl⟩ := hu
    exact hr y hy
  · exact hA
  · exact hupper htarget hne

end PolycyclicRecognition.CartanWordModel

end

end OAI
