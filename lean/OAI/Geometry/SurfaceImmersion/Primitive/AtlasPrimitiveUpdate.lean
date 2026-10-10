import OAI.Geometry.SurfaceImmersion.Correction.AtlasPrimitiveMean
import OAI.Geometry.SurfaceImmersion.Atlas.AtlasLinearMapBounds
import OAI.Geometry.SurfaceImmersion.Geometry.GlobalInputRecurrence

namespace OAI

/-! Propagation of the actual slow-map norms and normalized polynomial
error through one primitive increment. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation WeightedEstimates
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

omit [CompactSpace M] in
lemma weighted_increment_unscaled {X : M → Space} {τ C : ℝ} {m : ℕ}
    (hτ : 0 < τ) (hτ1 : τ ≤ 1) (hC : 0 ≤ C)
    (hX : A.WeightedBound τ m C X) : A.WeightedBound 1 m (C/τ^m) X := by
  intro i j hj x hx
  simp only [one_pow,one_mul]
  exact ((hX i).deriv_le hτ hj hx).trans
    (div_le_div_of_nonneg_left hC (pow_pos hτ _)
      (pow_le_pow_of_le_one hτ.le hτ1 hj))

/-- The output bounds concern the map that is actually added, and the
normalized defect of its actual polynomial metric. -/
theorem polynomial_increment_propagation {n : A.centers → ℕ}
    {Pol : ∀ i : A.centers, Fin 3 → Fin (n i) → Expression}
    (hPol : ∀ i k l, (Pol i k l).SmoothCoeffs univ)
    {γ : ∀ x : M, CovariantTwoTensor x}
    (hγ : ContMDiff planeModel (planeModel.prod 𝓘(ℝ,TensorFiber)) ∞
      (fun x => TotalSpace.mk' TensorFiber x (γ x)))
    {F G X : M → Space} (hF : ContMDiff planeModel spaceModel ∞ F)
    (hG : ContMDiff planeModel spaceModel ∞ G) (hX : ContMDiff planeModel spaceModel ∞ X)
    {s τ δ δ' ε c : ℝ} (hs : 0 < s) (hτ : 0 < τ) (hτs : τ ≤ s) (hτ1 : τ ≤ 1)
    (hδ : 0 < δ) (hδ' : 0 < δ')
    (P B E : ℕ → ℝ) (hP : ∀ m, 0 ≤ P m) (hB : ∀ m, 0 ≤ B m)
    (hclose : A.WeightedBound 1 2 c (G-F))
    (hmap : ∀ m, A.ShiftedBound 2 m s (P m) G)
    (hinc : ∀ m, A.WeightedBound τ m (B m*(δ*τ)) X)
    (herr : ∀ m, A.TensorWeightedBound τ m (E m)
      (A.atlasPolynomialMetric Pol ε (G+X)-A.atlasPolynomialMetric Pol ε G-
        δ^2 • A.polynomialMeanTarget Pol ε δ δ' γ G)) :
    A.WeightedBound 1 2 (c+B 2*δ/τ) (G+X-F) ∧
    (∀ m, A.ShiftedBound 2 m τ (P 0+P m+B (2+m)*δ/τ) (G+X)) ∧
    (∀ m, A.TensorWeightedBound τ m (E m/δ'^2)
      (A.normalizedPolynomialDefect Pol ε δ' γ (G+X))) := by
  have htC (m : ℕ) : 0 ≤ B m*(δ*τ) := mul_nonneg (hB m) (mul_nonneg hδ.le hτ.le)
  have hcX := A.weighted_increment_unscaled hτ hτ1 (htC 2) (hinc 2)
  have hcX' : A.WeightedBound 1 2 (B 2*δ/τ) X := by
    convert hcX using 1
    field_simp
  have hc := A.weightedBound_add (hG.sub hF) hX zero_le_one hclose hcX'
  have heq : G+X-F = (G-F)+X := by abel
  rw [heq]
  refine ⟨hc,?_,?_⟩
  · intro m
    have hx := A.weighted_to_shifted hτ hτ1 (htC (2+m)) (hinc (2+m))
    have hx' : A.ShiftedBound 2 m τ (B (2+m)*δ/τ) X := by
      convert hx using 1
      field_simp
    have hm := A.shifted_map_recurrence hG hX (hmap 0) (hmap m) hx'
      hs hτ.le hτs (hP 0) (hP m)
    intro i j hj x
    exact (hm i j hj x).trans (by
      have hr : τ/s ≤ 1 := (div_le_one hs).2 hτs
      have hh := mul_le_of_le_one_left (hP m) hr
      linarith)
  · intro m
    exact A.normalizedPolynomialDefect_after_step hPol hδ.ne' hδ'.ne'
      hγ hG (hG.add hX) (herr m)

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
