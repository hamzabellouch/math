import OAI.GroupTheory.PolycyclicRecognition.Algebra.OccupationTranslation

namespace OAI

/-! # Actual Haar-cell translation errors for chart occupation laws -/

noncomputable section

namespace PolycyclicRecognition

open MeasureTheory Module Filter
open scoped Manifold Topology

/-- Uniformly small normalized moves in the first nilpotent factor give
vanishing translation errors for the law of the sampled chart itself. -/
theorem model_cell_occupation_error_tendsto_zero
    {E N L D Y G ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace N] [ChartedSpace E N] [Group N]
    [LieGroup (𝓘(ℝ, E)) ⊤ N] [T2Space N] [SimplyConnectedSpace N]
    [MeasurableSpace N] [BorelSpace N] [LieRing L] [LieAlgebra ℝ L]
    [MeasurableSpace D] [TopologicalSpace Y] [CompactSpace Y]
    [MeasurableSpace Y] [BorelSpace Y] [SMul G Y] [ContinuousConstSMul G Y]
    (haar : NilpotentExponentialHaarInput E N)
    (Exp : GroupLieAlgebra (𝓘(ℝ, E)) N → N) (hExp : IsGroupExponential Exp)
    (e : L ≃ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, E)) N)
    (hnil : LieRing.IsNilpotent (GroupLieAlgebra (𝓘(ℝ, E)) N))
    {n c : ℕ} (b : ι → Basis (Fin n) ℝ L)
    (a : DynkinCoefficients c 2)
    (hm : ∀ x y, Exp (finiteDynkinPolynomial a ![x, y]) = Exp x * Exp y)
    {C : ℝ} (hbound : ∀ i, ‖basisBracket (b i)‖ ≤ C)
    {l : Filter ι} (q : ι → D → Fin n → ℝ)
    (hq : TendstoUniformly q (fun _ => 0) l)
    {S : Set (Fin n → ℝ)} (hS : MeasurableSet S)
    (hzero : volume S ≠ 0) (hfin : volume S ≠ ⊤)
    (ν : ProbabilityMeasure D) (p : ι → (Fin n → ℝ) × D → Y)
    (hp : ∀ i, Measurable (p i)) (g : G)
    (hmove : ∀ i x d, g • p i (x, d) =
      p i (dynkinProduct a (basisBracket (b i)) x (q i d), d))
    (f : C(Y, ℝ)) :
    Tendsto (fun i =>
      (∫ y, f (g • y) ∂(productOccupationLaw
        (cellProbabilityMeasure volume S hzero hfin) ν (p i) : Measure Y)) -
      ∫ y, f y ∂(productOccupationLaw
        (cellProbabilityMeasure volume S hzero hfin) ν (p i) : Measure Y)) l (𝓝 0) := by
  have hobs := model_cell_observable_error_tendstoUniformly haar Exp hExp e hnil
    b a hm hbound q hq hS hfin (fun i d x => f (p i (x, d)))
    (fun i d => (f.continuous.measurable.comp
      ((hp i).comp (measurable_id.prodMk measurable_const))).aestronglyMeasurable)
    (norm_nonneg f) (fun i d x => f.norm_coe_le_norm _)
  apply first_factor_product_occupation_error_tendsto_zero
    (cellProbabilityMeasure volume S hzero hfin) ν p hp
    (fun i d x => dynkinProduct a (basisBracket (b i)) x (q i d)) g hmove f
  apply tendstoUniformly_const_of_all_selections
  intro z
  have ht := (tendsto_selection_of_tendstoUniformly_const hobs z).const_mul (volume S).toReal⁻¹
  simp only [mul_zero] at ht
  convert ht using 1
  ext i
  simp only [integral_cellProbabilityMeasure]
  ring

end PolycyclicRecognition

end

end OAI
