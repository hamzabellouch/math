import OAI.GroupTheory.PolycyclicRecognition.Analysis.RescaledBoxTranslation
import OAI.GroupTheory.PolycyclicRecognition.Algebra.MappedBasisBrackets

namespace OAI

/-! # Small translations for an identified nilpotent Lie algebra

The Cartan root algebra is identified with the tangent Lie algebra of its
integrating group. Transporting the basis preserves the normalized bracket,
so the actual Haar-cell estimate applies before or after that identification.
-/

noncomputable section

namespace PolycyclicRecognition

open MeasureTheory Module Filter
open scoped Manifold Topology symmDiff

/-- The finite-cell translation estimate in the original model coordinates. -/
theorem model_rescaled_cell_translation_tendsto_zero
    {E G L ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace G] [ChartedSpace E G] [Group G]
    [LieGroup (𝓘(ℝ, E)) ⊤ G] [T2Space G] [SimplyConnectedSpace G]
    [MeasurableSpace G] [BorelSpace G] [LieRing L] [LieAlgebra ℝ L]
    (haar : NilpotentExponentialHaarInput E G)
    (Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G) (hExp : IsGroupExponential Exp)
    (e : L ≃ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, E)) G)
    (hnil : LieRing.IsNilpotent (GroupLieAlgebra (𝓘(ℝ, E)) G))
    {n c : ℕ} (b : ι → Basis (Fin n) ℝ L)
    (a : DynkinCoefficients c 2)
    (hm : ∀ x y, Exp (finiteDynkinPolynomial a ![x, y]) = Exp x * Exp y)
    {C : ℝ} (hbound : ∀ i, ‖basisBracket (b i)‖ ≤ C)
    {l : Filter ι} (q : ι → Fin n → ℝ) (hq : Tendsto q l (𝓝 0))
    {S : Set (Fin n → ℝ)} (hS : MeasurableSet S) (hfin : volume S ≠ ⊤) :
    Tendsto (fun i => volume (((fun x => dynkinProduct a (basisBracket (b i)) x (q i)) ⁻¹' S) ∆ S))
      l (𝓝 0) := by
  have hb (i : ι) : basisBracket ((b i).map e.toLinearEquiv) = basisBracket (b i) :=
    basisBracket_map_lieEquiv (b i) e
  have hmapped : ∀ i, ‖basisBracket ((b i).map e.toLinearEquiv)‖ ≤ C := by
    intro i
    rw [hb]
    exact hbound i
  have ht := actual_rescaled_cell_translation_tendsto_zero haar Exp hExp hnil
    (fun i => (b i).map e.toLinearEquiv) a hm hmapped q hq hS hfin
  simpa only [hb] using ht

end PolycyclicRecognition

end

end OAI
