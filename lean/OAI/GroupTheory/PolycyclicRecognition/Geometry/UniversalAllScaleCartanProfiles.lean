import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanDMetric
import OAI.GroupTheory.PolycyclicRecognition.Analysis.AllScaleProfileEquicontinuity
import OAI.GroupTheory.PolycyclicRecognition.Analysis.ProfilePointwiseBounds

namespace OAI

/-! # A compact profile family for every nonnegative real scale -/

noncomputable section

namespace PolycyclicRecognition

open Module LieAlgebra LieModule Filter
open scoped Manifold Topology NNReal

/-- Only the metric data used to form a normalized chart profile. -/
structure AllScaleProfileData (G W : Type*) [Group G] [PseudoMetricSpace G]
    [NormedAddCommGroup W] (K : ℝ≥0) (B : ℝ) where
  scale : ℝ
  nonneg : 0 ≤ scale
  map : G → W
  lipschitz : LipschitzWith K map
  center : G
  suffix : G
  suffix_bound : dist 1 suffix / Real.exp scale ≤ B

variable {EG G I W A : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [SimplyConnectedSpace G] [IsIsometricSMul G G]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  {ExpG : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H ExpG)
  [Fintype I] [DecidableEq I]

include T in
/-- All nonnegative scales share one modulus of continuity. -/
theorem equicontinuous_all_cartan_profiles
    (hExpG : IsGroupExponential ExpG)
    (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
    (haarD : NilpotentExponentialHaarInput F.D.modelSpace F.D.carrier)
    (dynkinD : NilpotentDynkinExpansionInput F.D.modelSpace F.D.carrier)
    (X : I → H) {k : ℕ} (hk : lowerCentralSeries ℝ H H k = ⊥)
    (hletters : ∀ i : I, FreeMagma.of i ∈ boundedBracketWords k)
    (b₀ : Basis (Fin (finrank ℝ H)) ℝ H)
    (β : WordBasisSelections X (boundedBracketWords k))
    (hβ : IsMaximizingColumnBasis (wordListCoordinates X (boundedBracketWords k) b₀)
      (fun w => bracketWordExponent (fun _ : I => 1) w) β.val)
    (scale : A → ℝ) (hs0 : ∀ u, 0 ≤ scale u)
    {K : ℝ≥0} (J : A → G → W) (hJ : ∀ u, LipschitzWith K (J u))
    (x suffix : A → G) :
    let b := WordBasisSelections.basis X (boundedBracketWords k) β
    let cost := fun j => bracketWordExponent (fun _ : I => 1) (β.val j)
    Equicontinuous (fun u => rescaledMapProfile (J u) (x u) (suffix u) (scale u)
      (fun z => F.inclusionD (F.ExpD (F.D.equiv
        ((exponentialRescaleBasis b cost (scale u)).equivFun.symm z))))) := by
  dsimp only
  let b := WordBasisSelections.basis X (boundedBracketWords k) β
  let cost := fun j => bracketWordExponent (fun _ : I => 1) (β.val j)
  let E : H → G := fun v => F.inclusionD (F.ExpD (F.D.equiv v))
  obtain ⟨⟨chartD, hchartD⟩, _⟩ := haarD.2 F.ExpD F.isExpD
    (F.D.tangent_nilpotent inferInstance)
  have hbij : Function.Bijective (F.ExpD ∘ F.D.equiv) :=
    (funext hchartD ▸ chartD.bijective).comp F.D.equiv.bijective
  obtain ⟨coeff, _, hprod⟩ := model_finiteDynkinExpansion dynkinD F.D.equiv F.ExpD
    F.isExpD hk 2
  have hm (v w : H) : E (finiteDynkinPolynomial coeff ![v, w]) = E v * E w := by
    simpa [E, List.ofFn_succ] using congrArg F.inclusionD (hprod ![v, w]).symm
  obtain ⟨C, hC, hmetric⟩ := exists_cartan_d_chart_metric_bound T F hExpG realize haarD
    dynkinD X hk hletters b₀ 1
  have hchart : Continuous (fun p : ℝ × (Fin (finrank ℝ H) → ℝ) =>
      E ((exponentialRescaleBasis b cost p.1).equivFun.symm p.2)) := by
    exact F.closedD.continuous.comp ((funext hchartD ▸ chartD.continuous).comp
      (continuous_mapped_scaled_basis_coordinates F.D.equiv.toLinearMap b cost))
  exact equicontinuous_all_scale_profiles b cost
    (maximizing_word_basis_bracket_weight X hk b₀ (fun _ => 1) β hβ) E
    (F.closedD.injective.comp hbij.injective)
    (by simp [E, F.isExpD.map_zero]) (fun v => by simp [E, F.isExpD.map_neg])
    (fun v s t => by simp only [E, map_smul, F.isExpD.map_add_smul, map_mul])
    coeff hm hC (hmetric β hβ) hchart scale hs0 J hJ x suffix

variable [ProperSpace W]

include T in
/-- The compact family is chosen before the real scale, the map, the
center, and the suffix. This makes subsequent enlargement thresholds
independent of any selected sequence. -/
theorem exists_universal_compact_cartan_profiles_all_scales
    (hExpG : IsGroupExponential ExpG)
    (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
    (haarD : NilpotentExponentialHaarInput F.D.modelSpace F.D.carrier)
    (dynkinD : NilpotentDynkinExpansionInput F.D.modelSpace F.D.carrier)
    (X : I → H) {k : ℕ} (hk : lowerCentralSeries ℝ H H k = ⊥)
    (hletters : ∀ i : I, FreeMagma.of i ∈ boundedBracketWords k)
    (b₀ : Basis (Fin (finrank ℝ H)) ℝ H)
    (β : WordBasisSelections X (boundedBracketWords k))
    (hβ : IsMaximizingColumnBasis (wordListCoordinates X (boundedBracketWords k) b₀)
      (fun w => bracketWordExponent (fun _ : I => 1) w) β.val)
    (K : ℝ≥0) (B : ℝ) :
    ∃ S : Set C((Fin (finrank ℝ H) → ℝ), W), IsCompact S ∧
      ∀ r : ℝ, 0 ≤ r → ∀ J : G → W, LipschitzWith K J → ∀ x a : G,
      dist 1 a / Real.exp r ≤ B → ∃ f ∈ S, ∀ z,
        f z = rescaledMapProfile J x a r
          (fun z => F.inclusionD (F.ExpD (F.D.equiv
            ((exponentialRescaleBasis (WordBasisSelections.basis X (boundedBracketWords k) β)
              (fun j => bracketWordExponent (fun _ : I => 1) (β.val j)) r).equivFun.symm z)))) z := by
  let : IsTopologicalGroup G := topologicalGroup_of_lieGroup (𝓘(ℝ, EG)) ⊤
  let P := AllScaleProfileData G W K B
  let b := WordBasisSelections.basis X (boundedBracketWords k) β
  let cost := fun j => bracketWordExponent (fun _ : I => 1) (β.val j)
  let φ := fun r z => F.inclusionD (F.ExpD (F.D.equiv
    ((exponentialRescaleBasis b cost r).equivFun.symm z)))
  have hφ (r : ℝ) : Continuous (φ r) :=
    F.closedD.continuous.comp (continuous_model_exp_coordinates haarD F.ExpD F.isExpD
      F.D.equiv (F.D.tangent_nilpotent inferInstance) (exponentialRescaleBasis b cost r))
  have hz (r : ℝ) : φ r 0 = 1 := by simp [φ, F.isExpD.map_zero]
  let raw : P → C((Fin (finrank ℝ H) → ℝ), W) := fun p =>
    ⟨rescaledMapProfile p.map p.center p.suffix p.scale (φ p.scale),
      continuous_rescaledMapProfile p.lipschitz.continuous _ _ _ (hφ p.scale)⟩
  have hequi : Equicontinuous (fun p z => raw p z) :=
    equicontinuous_all_cartan_profiles T F hExpG realize haarD dynkinD X hk hletters b₀ β hβ
      (fun p : P => p.scale) (fun p => p.nonneg) (fun p => p.map) (fun p => p.lipschitz)
      (fun p => p.center) (fun p => p.suffix)
  obtain ⟨S, hS, hmem⟩ := exists_compact_containing_profiles raw hequi (0 : W) (by
    intro z
    obtain ⟨D, _, hD⟩ := exists_cartan_d_chart_metric_bound T F hExpG realize haarD dynkinD
      X hk hletters b₀ ‖z‖
    refine ⟨(K : ℝ) * D + (K : ℝ) * B, ?_⟩
    intro p
    rw [dist_zero_right]
    have hchart : dist 1 (φ p.scale z) / Real.exp p.scale ≤ D := by
      apply (div_le_iff₀ (Real.exp_pos _)).mpr
      apply hD β hβ p.scale p.nonneg
      rw [LinearEquiv.apply_symm_apply]
    have hanchor := (rescaledMapProfile_zero_norm_le p.lipschitz p.center p.suffix
      p.scale (φ p.scale) (hz p.scale)).trans
      (mul_le_mul_of_nonneg_left p.suffix_bound K.coe_nonneg)
    exact (rescaledMapProfile_norm_le p.lipschitz p.center p.suffix p.scale
      (φ p.scale) (hz p.scale) z).trans
      (add_le_add (mul_le_mul_of_nonneg_left hchart K.coe_nonneg) hanchor))
  refine ⟨S, hS, ?_⟩
  intro r hr J hJ x a ha
  let p : P := ⟨r, hr, J, hJ, x, a, ha⟩
  exact ⟨raw p, hmem p, fun _ => rfl⟩

end PolycyclicRecognition

end

end OAI
