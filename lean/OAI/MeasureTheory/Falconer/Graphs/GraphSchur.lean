import OAI.MeasureTheory.Falconer.Graphs.GraphDegrees
import OAI.MeasureTheory.Falconer.Graphs.FinsetSchur
import Mathlib.MeasureTheory.Integral.Bochner.Basic

namespace OAI

/-!
# Positive Schur step for the all-dimensional graph estimate

The finite Schur inequality applies to arbitrary index types. The graph
geometry and degrees retain the ambient dimension. A partition of unity
costs no factor equal to the number of caps.
-/

namespace Falconer
open MeasureTheory
attribute [local instance] Classical.propDecidable

/-- Positive Schur bound for a complex amplitude on a finite graph. -/
theorem finite_graph_schur {ι : Type*} (S : Finset ι)
    (G : ι → ι → Prop) (F : ι → ℂ) (D : ℝ)
    (hrow : ∀ a ∈ S, ((S.filter (G a)).card : ℝ) ≤ D)
    (hcol : ∀ b ∈ S, ((S.filter (fun a => G a b)).card : ℝ) ≤ D) :
    (∑ a ∈ S, ∑ b ∈ S, if G a b then ‖F a * star (F b)‖ else 0) ≤
      D * ∑ a ∈ S, ‖F a‖^2 := by
  have h := PlanarFalconer.finset_bipartite_schur S S G
    (fun a => ‖F a‖) (fun a => ‖F a‖) D hrow hcol
  simp only [norm_mul, norm_star] at ⊢
  convert h using 1
  ring

/-- The retained grid graph satisfies Schur with the minimum of the two
parallel-test bounds, times the explicit remaining-cell packing factor. -/
theorem retainedGrid_schur {d L C₁ C₂ : ℕ} {s τ : ℝ} (hs : 0 < s)
    (hL : 4 * τ * s ≤ L) (A B : Finset (Fin d → ℤ))
    (w₁ w₂ : Space d) (hw₁ : ‖w₁‖ = 1) (hw₂ : ‖w₂‖ = 1)
    (h₁ : ∀ a ∈ A, (A.filter (fun z =>
      ‖perpendicularPart w₁ (scaledGridPoint s z - scaledGridPoint s a)‖ ≤ τ)).card ≤ C₁)
    (h₂ : ∀ b ∈ B, (B.filter (fun z =>
      ‖perpendicularPart w₂ (scaledGridPoint s z - scaledGridPoint s b)‖ ≤ τ)).card ≤ C₂)
    (F : ((Fin d → ℤ) × (Fin d → ℤ)) → ℂ) :
    (∑ row ∈ A ×ˢ B, ∑ col ∈ A ×ˢ B,
      if retainedGridEdge s w₁ w₂ τ row col then ‖F row * star (F col)‖ else 0) ≤
      ((2 * L + 1)^d * min C₁ C₂ : ℕ) * ∑ row ∈ A ×ˢ B, ‖F row‖^2 := by
  apply finite_graph_schur
  · intro row hrow
    obtain ⟨ha, hb⟩ := Finset.mem_product.mp hrow
    exact_mod_cast retainedGrid_degree_min hs hL A B w₁ w₂ hw₁ hw₂ row (h₁ _ ha) (h₂ _ hb)
  · intro col hcol
    obtain ⟨ha, hb⟩ := Finset.mem_product.mp hcol
    exact_mod_cast retainedGrid_column_degree_min hs hL A B w₁ w₂ hw₁ hw₂ col (h₁ _ ha) (h₂ _ hb)

/-- Summing a nonnegative angular partition of unity preserves the Schur
bound without a cap-count factor. -/
theorem partition_graph_schur {ι κ : Type*} (S : Finset ι) (K : Finset κ)
    (G : κ → ι → ι → Prop) (F : ι → ℂ) (weight : κ → ℝ) (D : ℝ)
    (hweight : ∀ k ∈ K, 0 ≤ weight k) (hpartition : ∑ k ∈ K, weight k = 1)
    (hrow : ∀ k ∈ K, ∀ a ∈ S, ((S.filter (G k a)).card : ℝ) ≤ D)
    (hcol : ∀ k ∈ K, ∀ b ∈ S, ((S.filter (fun a => G k a b)).card : ℝ) ≤ D) :
    ‖∑ k ∈ K, weight k • (∑ a ∈ S, ∑ b ∈ S,
      if G k a b then F a * star (F b) else 0)‖ ≤ D * ∑ a ∈ S, ‖F a‖^2 := by
  calc
    _ ≤ ∑ k ∈ K, ‖weight k • (∑ a ∈ S, ∑ b ∈ S,
        if G k a b then F a * star (F b) else 0)‖ := norm_sum_le _ _
    _ ≤ ∑ k ∈ K, weight k * (D * ∑ a ∈ S, ‖F a‖^2) := by
      apply Finset.sum_le_sum
      intro k hk
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hweight k hk)]
      apply mul_le_mul_of_nonneg_left _ (hweight k hk)
      calc
        _ ≤ ∑ a ∈ S, ∑ b ∈ S, ‖if G k a b then F a * star (F b) else 0‖ := by
          exact (norm_sum_le _ _).trans (Finset.sum_le_sum (fun a _ => norm_sum_le _ _))
        _ = ∑ a ∈ S, ∑ b ∈ S, if G k a b then ‖F a * star (F b)‖ else 0 := by
          simp only [apply_ite norm, norm_zero]
        _ ≤ _ := finite_graph_schur S (G k) F D (hrow k hk) (hcol k hk)
    _ = _ := by rw [← Finset.sum_mul, hpartition, one_mul]

/-- Integrated retained-edge estimate. The domain can include both angular
variables and the radial variable with its nonnegative cutoff measure. -/
theorem integral_partition_graph_schur {X ι κ : Type*} [MeasurableSpace X]
    (μ : Measure X) (S : Finset ι) (K : Finset κ)
    (G : κ → ι → ι → Prop) (F : ι → X → ℂ) (weight : κ → X → ℝ) (D : ℝ)
    (hF : ∀ a ∈ S, Integrable (fun x => ‖F a x‖^2) μ)
    (hweight : ∀ x k, k ∈ K → 0 ≤ weight k x)
    (hpartition : ∀ x, ∑ k ∈ K, weight k x = 1)
    (hrow : ∀ k ∈ K, ∀ a ∈ S, ((S.filter (G k a)).card : ℝ) ≤ D)
    (hcol : ∀ k ∈ K, ∀ b ∈ S, ((S.filter (fun a => G k a b)).card : ℝ) ≤ D) :
    ‖∫ x, ∑ k ∈ K, weight k x • (∑ a ∈ S, ∑ b ∈ S,
      if G k a b then F a x * star (F b x) else 0) ∂μ‖ ≤
      D * ∑ a ∈ S, ∫ x, ‖F a x‖^2 ∂μ := by
  have hbound := norm_integral_le_of_norm_le ((integrable_finsetSum S hF).const_mul D)
    (Filter.Eventually.of_forall (fun x => partition_graph_schur S K G
      (fun a => F a x) (fun k => weight k x) D (hweight x) (hpartition x) hrow hcol))
  simpa only [integral_const_mul, integral_finsetSum S hF] using hbound

end Falconer

end OAI
