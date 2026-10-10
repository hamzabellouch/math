import OAI.GroupTheory.PolycyclicRecognition.Analysis.BasisDynkinHaar
import OAI.GroupTheory.PolycyclicRecognition.Algebra.PolynomialTranslationLimits

namespace OAI

/-! # Small translations of actual rescaled nilpotent boxes

The coordinate basis can vary without convergence. Bounded normalized
brackets and a vanishing translation coordinate suffice for the fixed cube.
All measure preservation is proved from the published exponential Haar input.
-/

noncomputable section

namespace PolycyclicRecognition

open MeasureTheory Module Filter Set
open scoped Manifold Topology symmDiff

/-- The actual normalized cells are asymptotically unchanged by right
translations whose normalized logarithms tend to zero. -/
theorem actual_rescaled_cell_translation_tendsto_zero
    {E G ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace G] [ChartedSpace E G] [Group G]
    [LieGroup (𝓘(ℝ, E)) ⊤ G] [T2Space G] [SimplyConnectedSpace G]
    [MeasurableSpace G] [BorelSpace G]
    (haar : NilpotentExponentialHaarInput E G)
    (Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G) (hExp : IsGroupExponential Exp)
    (hnil : LieRing.IsNilpotent (GroupLieAlgebra (𝓘(ℝ, E)) G))
    {n c : ℕ} (b : ι → Basis (Fin n) ℝ (GroupLieAlgebra (𝓘(ℝ, E)) G))
    (a : DynkinCoefficients c 2)
    (hm : ∀ x y, Exp (finiteDynkinPolynomial a ![x, y]) = Exp x * Exp y)
    {C : ℝ} (hbound : ∀ i, ‖basisBracket (b i)‖ ≤ C)
    {l : Filter ι} (q : ι → Fin n → ℝ) (hq : Tendsto q l (𝓝 0))
    {S : Set (Fin n → ℝ)} (hS : MeasurableSet S) (hfin : volume S ≠ ⊤) :
    Tendsto (fun i => volume (((fun x => dynkinProduct a (basisBracket (b i)) x (q i)) ⁻¹' S) ∆ S))
      l (𝓝 0) := by
  obtain ⟨⟨chart, hchart⟩, _⟩ := haar.2 Exp hExp hnil
  have hinj : Function.Injective Exp := by
    rw [← show chart = Exp from funext hchart]
    exact chart.injective
  let V := Fin n → ℝ
  let : FiniteDimensional ℝ (V →L[ℝ] V) := ContinuousLinearMap.finiteDimensional
  let : FiniteDimensional ℝ (V →L[ℝ] V →L[ℝ] V) := ContinuousLinearMap.finiteDimensional
  let : PseudoMetricSpace (V →L[ℝ] V →L[ℝ] V) :=
    (inferInstance : NormedAddCommGroup (V →L[ℝ] V →L[ℝ] V)).toPseudoMetricSpace
  let : ProperSpace (V →L[ℝ] V →L[ℝ] V) := FiniteDimensional.proper ℝ _
  let P := Metric.closedBall (0 : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) C ∩
    {B | PolynomialGroupLaws (dynkinProduct a B)}
  have hP : IsCompact P :=
    (isCompact_closedBall _ _).inter_right (isClosed_dynkinGroupLaws a)
  have hB (i : ι) : basisBracket (b i) ∈ P := by
    refine ⟨?_, ?_⟩
    · rw [Metric.mem_closedBall, dist_eq_norm]
      have hz : basisBracket (b i) - (0 : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) =
          basisBracket (b i) := by
        ext x y j
        simp
      rw [hz]
      exact hbound i
    · exact basis_polynomialGroupLaws (b i) Exp hinj hExp.map_zero hExp.map_neg
        hExp.map_add_smul a hm
  apply measure_dynkin_translation_symmDiff_tendsto_zero volume a P hP
    (fun B hB x => hB.2.2.2.1 x) (fun i => basisBracket (b i)) hB q hq
    (fun i => measurePreserving_basis_dynkin_right haar Exp hExp hnil (b i) a hm (q i)) hS hfin

end PolycyclicRecognition

end

end OAI
