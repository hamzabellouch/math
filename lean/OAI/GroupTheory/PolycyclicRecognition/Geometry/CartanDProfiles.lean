import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanDMetric
import OAI.GroupTheory.PolycyclicRecognition.Analysis.RescaledProfiles

namespace OAI

/-! # Equicontinuity of profiles on the actual Cartan factor -/

noncomputable section

namespace PolycyclicRecognition

open Module LieAlgebra LieModule Filter
open scoped Manifold Topology NNReal

variable {EG G I W A : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [SimplyConnectedSpace G] [IsIsometricSMul G G]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  {ExpG : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H ExpG)
  [Fintype I] [DecidableEq I]

include T in
/-- The chart profiles have a common modulus of continuity for arbitrary
sampled suffixes, centers, and uniformly Lipschitz maps. The metric estimate,
limiting group law, and fixed-scale continuity are all derived here. -/
theorem equicontinuous_cartan_d_profiles
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
    (scale : ℕ → ℝ) (hscale : Tendsto scale atTop atTop)
    {K : ℝ≥0} (J : ℕ → A → G → W) (hJ : ∀ i u, LipschitzWith K (J i u))
    (x suffix : ℕ → A → G) :
    let b := WordBasisSelections.basis X (boundedBracketWords k) β
    let cost := fun j => bracketWordExponent (fun _ : I => 1) (β.val j)
    Equicontinuous (fun p : ℕ × A =>
      rescaledMapProfile (J p.1 p.2) (x p.1 p.2) (suffix p.1 p.2) (scale p.1)
        (fun z => F.inclusionD (F.ExpD (F.D.equiv
          ((exponentialRescaleBasis b cost (scale p.1)).equivFun.symm z))))) := by
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
  apply equicontinuous_rescaled_profiles b cost
    (maximizing_word_basis_bracket_weight X hk b₀ (fun _ => 1) β hβ) E
    (F.closedD.injective.comp hbij.injective)
    (by simp [E, F.isExpD.map_zero]) (fun v => by simp [E, F.isExpD.map_neg])
    (fun v s t => by simp only [E, map_smul, F.isExpD.map_add_smul, map_mul])
    coeff hm hC (hmetric β hβ) scale hscale _ J hJ x suffix
  intro i
  exact F.closedD.continuous.comp (continuous_model_exp_coordinates haarD F.ExpD F.isExpD
    F.D.equiv (F.D.tangent_nilpotent inferInstance) (exponentialRescaleBasis b cost (scale i)))

end PolycyclicRecognition

end

end OAI
