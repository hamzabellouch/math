import OAI.Geometry.SurfaceImmersion.Primitive.PrimitiveSeedBounds
import OAI.Geometry.SurfaceImmersion.Correction.AtlasPolynomialValueBounds
import OAI.Geometry.SurfaceImmersion.Correction.AtlasPrimitiveMean
import OAI.Geometry.SurfaceImmersion.Geometry.InitialInputBounds

namespace OAI

/-! Uniform local jets and global displacement of the actual contracted
primitive seed, and its initial normalized polynomial defect. -/
noncomputable section
open Set Manifold Bundle TopologicalSpace
open scoped ContDiff Manifold Topology BigOperators

namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation WeightedEstimates PrimitiveRealization
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]

local instance primitiveSeedFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance primitiveSeedFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
local instance primitiveSeedDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance primitiveSeedDualSmul : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
local instance primitiveSeedSectionNormed (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance primitiveSeedSectionSpace (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)

namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

omit [CompactSpace M] in
lemma jetChartMap_const_smul (i : A.centers) (c : ℝ) (F : M → Space) :
    A.jetChartMap i (c • F) = c • A.jetChartMap i F := by
  funext x
  change spaceCoordinates (localize (i : M) (A.outer i) (c • F) x) =
    c • spaceCoordinates (localize (i : M) (A.outer i) F x)
  rw [localize_smul]
  exact map_smul spaceCoordinates c _

omit [CompactSpace M] in
lemma jetChartMap_primitiveSeed (i : A.centers) (δ : ℝ) (F : M → Space) :
    A.jetChartMap i (Real.sqrt (1-δ^2) • F) = primitiveSeed δ (A.jetChartMap i F) := by
  rw [A.jetChartMap_const_smul]
  rfl

/-- The compact low-jet range, all local derivative profiles, and the global
quadratic displacement profile are chosen before the contraction parameter. -/
theorem atlas_primitive_seed_bounds
    (F : M → Space) (hF : ContMDiff planeModel spaceModel ∞ F)
    (U : A.centers → Set JetPolynomial.Base) (hU : ∀ i, IsOpen (U i))
    (K : A.centers → Compacts JetPolynomial.Base) (hUK : ∀ i, U i ⊆ K i) :
    ∃ Q : Set LowJet, IsCompact Q ∧
    ∃ J B : A.centers → ℕ → ℝ, ∃ D : ℕ → ℝ,
      (∀ i m, 1 ≤ J i m) ∧ (∀ i m, 1 ≤ B i m) ∧ (∀ m, 0 ≤ D m) ∧
      ∀ δ : ℝ, δ^2 ≤ 1 →
        ContMDiff planeModel spaceModel ∞ (Real.sqrt (1-δ^2) • F) ∧
        (∀ i, MapsTo (lowJet (A.jetChartMap i (Real.sqrt (1-δ^2) • F))) (U i) Q) ∧
        (∀ i m, WeightedEstimates.WeightedBound (U i) 1 m (B i m)
          (lowJet (A.jetChartMap i (Real.sqrt (1-δ^2) • F)))) ∧
        (∀ i m, WeightedEstimates.WeightedBound (U i) 1 (m+2) (J i m)
          (A.jetChartMap i (Real.sqrt (1-δ^2) • F))) ∧
        (∀ m, A.WeightedBound 1 m (D m * δ^2) (Real.sqrt (1-δ^2) • F-F)) := by
  classical
  choose Q hQ J B hJ hB hlocal using fun i =>
    compact_primitiveSeed_bounds (hU i) (K i) (hUK i) (A.jetChartMap_smooth i hF)
  choose D hD hglobal using fun m => A.exists_shifted_bound m 0 hF
  let Q₀ : Set LowJet := ⋃ i, Q i
  refine ⟨Q₀,isCompact_iUnion hQ,J,B,D,hJ,hB,hD,?_⟩
  intro δ hδ
  have hseed (i) := hlocal i δ hδ
  have hid (i) := A.jetChartMap_primitiveSeed i δ F
  refine ⟨space_smul_contMDiff hF _,?_,?_,?_,?_⟩
  · intro i x hx
    rw [hid i]
    exact mem_iUnion.mpr ⟨i,(hseed i).1 hx⟩
  · intro i m
    rw [hid i]
    exact (hseed i).2.1 m
  · intro i m
    rw [hid i]
    exact (hseed i).2.2.1 m
  · intro m
    have hb : A.WeightedBound 1 m (D m) F := A.shifted_zero_to_weighted (hglobal m)
    have hh := A.weightedBound_const_smul hF hb (Real.sqrt (1-δ^2)-1)
    have heq : Real.sqrt (1-δ^2) • F-F = (Real.sqrt (1-δ^2)-1) • F := by
      rw [sub_smul,one_smul]
    rw [heq]
    intro i
    apply (hh i).mono_const
    calc
      |Real.sqrt (1-δ^2)-1| * D m ≤ δ^2 * D m :=
        mul_le_mul_of_nonneg_right (primitiveSeed_factor_bound hδ).2 (hD m)
      _ = D m * δ^2 := mul_comm _ _

/-- The normalized defect of the contracted seed is globally of order
`ε/δ²`, with a fixed all-order profile. -/
theorem atlas_primitive_seed_defect_bounds {n : A.centers → ℕ}
    (P : ∀ i : A.centers, Fin 3 → Fin (n i) → Expression)
    (hP : ∀ i k l, (P i k l).SmoothCoeffs univ)
    (F : M → Space) (hF : ContMDiff planeModel spaceModel ∞ F)
    (U : A.centers → Set JetPolynomial.Base) (hU : ∀ i, IsOpen (U i))
    (K : A.centers → Compacts JetPolynomial.Base) (hUK : ∀ i, U i ⊆ K i)
    (houter : ∀ i : A.centers, (chart (i : M)) '' tsupport (A.outer i) ⊆ U i) :
    ∃ D E : ℕ → ℝ, (∀ m, 0 ≤ D m) ∧ (∀ m, 0 ≤ E m) ∧
      ∀ (δ ε : ℝ), δ ≠ 0 → δ^2 ≤ 1 → 0 ≤ ε → ε ≤ 1 →
        (∀ m, A.WeightedBound 1 m (D m * δ^2) (Real.sqrt (1-δ^2) • F-F)) ∧
        (∀ m, A.TensorWeightedBound 1 m (E m * ε / δ^2)
          (A.normalizedPolynomialDefect P ε δ (inducedTensor F)
            (Real.sqrt (1-δ^2) • F))) := by
  obtain ⟨Q,hQ,J,B,D,hJ,hB,hD,hseed⟩ := A.atlas_primitive_seed_bounds F hF U hU K hUK
  obtain ⟨E,hE,hvalue⟩ := A.atlas_polynomial_value_bounds P hP U hU houter (fun _ => Q)
    (fun _ => hQ) (fun i m => B i (m+tensorOrder (P i)))
    (fun i m => hB i (m+tensorOrder (P i)))
  refine ⟨D,E,hD,hE,?_⟩
  intro δ ε hδ hδ1 hε hε1
  obtain ⟨hG,hGQ,hGb,_,hdisp⟩ := hseed δ hδ1
  refine ⟨hdisp,?_⟩
  intro m
  have hv := hvalue (Real.sqrt (1-δ^2) • F) hG hGQ 1 ε zero_lt_one le_rfl hε hε1
    (fun i m => hGb i (m+tensorOrder (P i))) m
  have hh := A.tensorWeightedBound_const_smul (A.atlasPolynomialValue_smooth hP hG ε) hv
    (-(δ^2)⁻¹)
  rw [← A.normalizedPolynomialDefect_seed P ε hF hδ hδ1] at hh
  convert hh using 1
  rw [abs_neg,abs_of_pos (inv_pos.mpr (sq_pos_of_ne_zero hδ))]
  simp only [one_pow,div_one]
  ring

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
