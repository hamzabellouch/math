import OAI.GroupTheory.PolycyclicRecognition.Algebra.RescaledDensityOccupation
import OAI.GroupTheory.PolycyclicRecognition.Analysis.OccupationSampling

namespace OAI

/-! # Fixed second-factor moves in the actual sampled chart law -/

noncomputable section

namespace PolycyclicRecognition

open MeasureTheory Module LieModule Filter
open scoped Manifold Topology

/-- For the independent chart law, every fixed move in the positively
weighted second nilpotent factor has vanishing translated-observable
error. All coordinate invariance and limiting assertions are derived
from the actual exponential and the published Haar input. -/
theorem model_density_occupation_error_tendsto_zero
    {E D L I A Y G ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace D] [ChartedSpace E D] [Group D]
    [LieGroup (𝓘(ℝ, E)) ⊤ D] [T2Space D] [SimplyConnectedSpace D]
    [MeasurableSpace D] [BorelSpace D] [LieRing L] [LieAlgebra ℝ L]
    [Fintype I] [DecidableEq I] [MeasurableSpace A]
    [TopologicalSpace Y] [CompactSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    [SMul G Y] [ContinuousConstSMul G Y]
    (haar : NilpotentExponentialHaarInput E D)
    (Exp : GroupLieAlgebra (𝓘(ℝ, E)) D → D) (hExp : IsGroupExponential Exp)
    (e : L ≃ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, E)) D)
    (hnil : LieRing.IsNilpotent (GroupLieAlgebra (𝓘(ℝ, E)) D))
    (X : I → L) {k c : ℕ} (hk : lowerCentralSeries ℝ L L k = ⊥)
    (hletters : ∀ i : I, FreeMagma.of i ∈ boundedBracketWords k)
    (b₀ : Basis (Fin (finrank ℝ L)) ℝ L)
    (s : I → ℝ) (hs : ∀ i, 0 < s i)
    {l : Filter ι} [l.IsCountablyGenerated] (scale : ι → ℝ)
    (hscale : Tendsto scale l atTop)
    (β : WordBasisSelections X (boundedBracketWords k))
    (hβ : IsMaximizingColumnBasis (wordListCoordinates X (boundedBracketWords k) b₀)
      (fun w => bracketWordExponent s w) β.val)
    (a : DynkinCoefficients c 2)
    (hm : ∀ x y, Exp (finiteDynkinPolynomial a ![x, y]) = Exp x * Exp y)
    (v : L) (μ : ProbabilityMeasure A) (ρ : (Fin (finrank ℝ L) → ℝ) → ℝ)
    (hc : Continuous ρ) (hi : Integrable ρ volume) (hp : ∀ z, 0 ≤ ρ z)
    (hmass : ∫ z, ρ z = 1)
    (p : ι → A × (Fin (finrank ℝ L) → ℝ) → Y) (hmeas : ∀ i, Measurable (p i))
    (g : G)
    (hmove : ∀ i x z, g • p i (x, z) = p i (x, dynkinProduct a
      (basisBracket (exponentialRescaleBasis
        (WordBasisSelections.basis X (boundedBracketWords k) β)
        (fun j => bracketWordExponent s (β.val j)) (max (scale i) 0))) z
      ((exponentialRescaleBasis (WordBasisSelections.basis X (boundedBracketWords k) β)
        (fun j => bracketWordExponent s (β.val j)) (max (scale i) 0)).equivFun v)))
    (f : C(Y, ℝ)) :
    Tendsto (fun i =>
      (∫ y, f (g • y) ∂(productOccupationLaw μ
        (densityProbabilityMeasure volume ρ hi hp hmass) (p i) : Measure Y)) -
      ∫ y, f y ∂(productOccupationLaw μ
        (densityProbabilityMeasure volume ρ hi hp hmass) (p i) : Measure Y)) l (𝓝 0) := by
  let b := fun i => exponentialRescaleBasis
    (WordBasisSelections.basis X (boundedBracketWords k) β)
    (fun j => bracketWordExponent s (β.val j)) (max (scale i) 0)
  let F : ι → (Fin (finrank ℝ L) → ℝ) → ℝ :=
    fun i z => ∫ x, f (p i (x, z)) ∂(μ : Measure A)
  have hF (i : ι) : AEStronglyMeasurable (F i) volume :=
    ((f.continuous.measurable.comp (hmeas i)).stronglyMeasurable.integral_prod_left').aestronglyMeasurable
  have hbound (i : ι) (z : Fin (finrank ℝ L) → ℝ) : ‖F i z‖ ≤ ‖f‖ := by
    have hh := norm_integral_le_of_norm_le_const (μ := (μ : Measure A))
      (f := fun x => f (p i (x, z))) (C := ‖f‖)
      (Eventually.of_forall (fun _ => f.norm_coe_le_norm _))
    simpa only [measureReal_def, measure_univ, ENNReal.toReal_one, mul_one] using hh
  have ht := model_rescaled_density_occupation_error_tendsto_zero haar Exp hExp e hnil
    X hk hletters b₀ s hs scale hscale β hβ a hm v ρ hc hi hp F hF (norm_nonneg f) hbound
  apply ht.congr
  intro i
  let fg : C(Y, ℝ) := ⟨fun y => f (g • y),
    f.continuous.comp (continuous_const_smul g)⟩
  have hfg := integral_productOccupationLaw_symm μ
    (densityProbabilityMeasure volume ρ hi hp hmass) (p i) (hmeas i) fg
  have hff := integral_productOccupationLaw_symm μ
    (densityProbabilityMeasure volume ρ hi hp hmass) (p i) (hmeas i) f
  change _ = _ - _
  rw [show (fun y => f (g • y)) = (fg : Y → ℝ) from rfl, hfg, hff]
  simp_rw [integral_densityProbabilityMeasure, fg, ContinuousMap.coe_mk, hmove]
  rfl

end PolycyclicRecognition

end

end OAI
