import OAI.GroupTheory.PolycyclicRecognition.Analysis.ModelBoxTranslation
import OAI.GroupTheory.PolycyclicRecognition.Analysis.CellOccupationError
import OAI.GroupTheory.PolycyclicRecognition.Algebra.UniformSelection

namespace OAI

/-! # Uniform small translations of actual model cells -/

noncomputable section

namespace PolycyclicRecognition

open MeasureTheory Module Filter
open scoped Manifold Topology symmDiff

variable {E G L ι Z : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace G] [ChartedSpace E G] [Group G]
  [LieGroup (𝓘(ℝ, E)) ⊤ G] [T2Space G] [SimplyConnectedSpace G]
  [MeasurableSpace G] [BorelSpace G] [LieRing L] [LieAlgebra ℝ L]

/-- A common vanishing normalized coordinate bound gives uniform boundary
loss in every sampled parameter. No convergence of the basis is required. -/
theorem model_cell_boundary_loss_tendstoUniformly
    (haar : NilpotentExponentialHaarInput E G)
    (Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G) (hExp : IsGroupExponential Exp)
    (e : L ≃ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, E)) G)
    (hnil : LieRing.IsNilpotent (GroupLieAlgebra (𝓘(ℝ, E)) G))
    {n c : ℕ} (b : ι → Basis (Fin n) ℝ L)
    (a : DynkinCoefficients c 2)
    (hm : ∀ x y, Exp (finiteDynkinPolynomial a ![x, y]) = Exp x * Exp y)
    {C : ℝ} (hbound : ∀ i, ‖basisBracket (b i)‖ ≤ C)
    {l : Filter ι} (q : ι → Z → Fin n → ℝ)
    (hq : TendstoUniformly q (fun _ => 0) l)
    {S : Set (Fin n → ℝ)} (hS : MeasurableSet S) (hfin : volume S ≠ ⊤) :
    TendstoUniformly (fun i z =>
      (volume (((fun x => dynkinProduct a (basisBracket (b i)) x (q i z)) ⁻¹' S) ∆ S)).toReal)
      (fun _ => 0) l := by
  apply tendstoUniformly_const_of_all_selections
  intro z
  have ht := model_rescaled_cell_translation_tendsto_zero haar Exp hExp e hnil b a hm
    hbound (fun i => q i (z i)) (tendsto_selection_of_tendstoUniformly_const hq z) hS hfin
  have hh := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp ht
  convert hh using 1
  · ext i
    rfl
  · simp only [ENNReal.toReal_zero]

/-- Uniformity also holds after projection to any bounded observable, even
when that observable depends on the scale and the sampled parameter. -/
theorem model_cell_observable_error_tendstoUniformly
    (haar : NilpotentExponentialHaarInput E G)
    (Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G) (hExp : IsGroupExponential Exp)
    (e : L ≃ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, E)) G)
    (hnil : LieRing.IsNilpotent (GroupLieAlgebra (𝓘(ℝ, E)) G))
    {n c : ℕ} (b : ι → Basis (Fin n) ℝ L)
    (a : DynkinCoefficients c 2)
    (hm : ∀ x y, Exp (finiteDynkinPolynomial a ![x, y]) = Exp x * Exp y)
    {C : ℝ} (hbound : ∀ i, ‖basisBracket (b i)‖ ≤ C)
    {l : Filter ι} (q : ι → Z → Fin n → ℝ)
    (hq : TendstoUniformly q (fun _ => 0) l)
    {S : Set (Fin n → ℝ)} (hS : MeasurableSet S) (hfin : volume S ≠ ⊤)
    (f : ι → Z → (Fin n → ℝ) → ℝ)
    (hf : ∀ i z, AEStronglyMeasurable (f i z) volume)
    {D : ℝ} (hD : 0 ≤ D) (hfbound : ∀ i z x, ‖f i z x‖ ≤ D) :
    TendstoUniformly (fun i z =>
      (∫ x in S, f i z (dynkinProduct a (basisBracket (b i)) x (q i z))) -
        ∫ x in S, f i z x) (fun _ => 0) l := by
  apply tendstoUniformly_const_of_all_selections
  intro z
  have hp (i : ι) : MeasurePreserving
      (fun x => dynkinProduct a (basisBracket (b i)) x (q i (z i))) volume volume := by
    have hh := measurePreserving_basis_dynkin_right haar Exp hExp hnil
      ((b i).map e.toLinearEquiv) a hm (q i (z i))
    simpa only [basisBracket_map_lieEquiv] using hh
  have ht := model_rescaled_cell_translation_tendsto_zero haar Exp hExp e hnil b a hm
    hbound (fun i => q i (z i)) (tendsto_selection_of_tendstoUniformly_const hq z) hS hfin
  exact cell_translation_integral_error_tendsto_zero volume _ hp hS
    (lt_top_iff_ne_top.mpr hfin) (fun i => f i (z i)) (fun i => hf i (z i))
    hD (fun i => hfbound i (z i)) ht

end PolycyclicRecognition

end

end OAI
