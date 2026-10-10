import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanUniformGeneration
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanFactorCharts
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanSupportLegs
import OAI.GroupTheory.PolycyclicRecognition.Analysis.NilpotentWordMetric
import OAI.GroupTheory.PolycyclicRecognition.Analysis.RescaledMetricSmallness

namespace OAI

/-! # Metric control of the actual Cartan factor charts -/

noncomputable section

namespace PolycyclicRecognition

open Module LieAlgebra LieModule Filter
open scoped Manifold Matrix.Norms.Operator Topology

attribute [local instance 100] LieRing.ofAssociativeRing

variable {EG G I : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [SimplyConnectedSpace G] [IsIsometricSMul G G]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  {ExpG : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H ExpG)
  [Fintype I] [DecidableEq I]

include T in
/-- Bounded normalized coordinates in the Cartan factor have ambient
distance at most a constant times the dilation scale. This follows from
the actual finite generator words, not a metric-scaling hypothesis. -/
theorem exists_cartan_d_chart_metric_bound
    (hExpG : IsGroupExponential ExpG)
    (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
    (haarD : NilpotentExponentialHaarInput F.D.modelSpace F.D.carrier)
    (dynkinD : NilpotentDynkinExpansionInput F.D.modelSpace F.D.carrier)
    (X : I → H) {k : ℕ} (hk : lowerCentralSeries ℝ H H k = ⊥)
    (hletters : ∀ i : I, FreeMagma.of i ∈ boundedBracketWords k)
    (b₀ : Basis (Fin (finrank ℝ H)) ℝ H) (R : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (β : WordBasisSelections X (boundedBracketWords k)),
      IsMaximizingColumnBasis (wordListCoordinates X (boundedBracketWords k) b₀)
        (fun w => bracketWordExponent (fun _ : I => 1) w) β.val →
      ∀ r : ℝ, 0 ≤ r → ∀ v : H,
      ‖(exponentialRescaleBasis (WordBasisSelections.basis X (boundedBracketWords k) β)
        (fun i => bracketWordExponent (fun _ : I => 1) (β.val i)) r).equivFun v‖ ≤ R →
      dist 1 (F.inclusionD (F.ExpD (F.D.equiv v))) ≤ C * Real.exp r := by
  obtain ⟨m, hm, ρ, j, hind, hmatch⟩ := realize ⟨a, ⟨T⟩⟩ ExpG hExpG
  let _ : NeZero m := ⟨Nat.ne_of_gt hm⟩
  have hρ : Function.Injective ρ := by
    intro g h he
    exact hind.injective (congrArg (fun u : (Matrix (Fin m) (Fin m) ℝ)ˣ =>
      (u : Matrix (Fin m) (Fin m) ℝ)) he)
  obtain ⟨⟨chartD, hchartD⟩, _⟩ := haarD.2 F.ExpD F.isExpD
    (F.D.tangent_nilpotent inferInstance)
  have hbij : Function.Bijective (F.ExpD ∘ F.D.equiv) :=
    (funext hchartD ▸ chartD.bijective).comp F.D.equiv.bijective
  let E : H → G := fun v => F.inclusionD (F.ExpD (F.D.equiv v))
  have hcont (i : I) : Continuous (fun t : ℝ => E (t • X i)) := by
    simpa [E, F.compatibleD] using
      continuous_exp_line_of_published_realization T ExpG hExpG realize (X i)
  obtain ⟨coeff, _, hprod⟩ := model_finiteDynkinExpansion dynkinD F.D.equiv F.ExpD
    F.isExpD hk 2
  apply exists_unit_weight_chart_metric_bound X hk hletters b₀ E
    (F.closedD.injective.comp hbij.injective)
    (by simp [E, F.isExpD.map_zero]) (fun v => by simp [E, F.isExpD.map_neg])
    (fun v s t => by simp only [E, map_smul, F.isExpD.map_add_smul, map_mul])
    hcont coeff (fun x y => ?_) (j.comp H.incl) ρ hρ (fun v => ?_) R
  · have hh := congrArg F.inclusionD (hprod ![x, y]).symm
    simpa [E, List.ofFn_succ] using hh
  · dsimp only [E]
    rw [F.compatibleD, hmatch]
    rfl

include T in
/-- Small normalized Cartan coordinates give sublinear ambient distance.
This is the equicontinuity estimate needed after taking a limit of the
finite-dimensional coordinate group laws. -/
theorem cartan_d_metric_sublinear_of_coordinates
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
    {ι : Type*} {l : Filter ι} (scale : ι → ℝ) (hscale : Tendsto scale l atTop)
    (v : ι → H)
    (hsmall : Tendsto (fun i =>
      (exponentialRescaleBasis (WordBasisSelections.basis X (boundedBracketWords k) β)
        (fun j => bracketWordExponent (fun _ : I => 1) (β.val j)) (scale i)).equivFun (v i))
      l (𝓝 0)) :
    Tendsto (fun i => dist 1 (F.inclusionD (F.ExpD (F.D.equiv (v i)))) /
      Real.exp (scale i)) l (𝓝 0) := by
  obtain ⟨C, hC, hmetric⟩ := exists_cartan_d_chart_metric_bound T F hExpG realize haarD
    dynkinD X hk hletters b₀ 1
  exact metric_sublinear_of_rescaled_coordinates_tendsto_zero _ _ _ hC
    (hmetric β hβ) scale hscale v hsmall

end PolycyclicRecognition

end

end OAI
