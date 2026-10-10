import OAI.Geometry.SurfaceImmersion.Atlas.GridCutoffSupport
import OAI.Geometry.SurfaceImmersion.Correction.PolynomialBudgetAlgebra

namespace OAI

/-! The exact supported cell cutoffs have a fixed atlas polynomial bound. -/
noncomputable section
open Set Manifold
open scoped ContDiff Manifold Topology NNReal BigOperators
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation PhaseGrid WeightedEstimates
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

theorem grid_exact_cutoff_bounds :
    ∃ P : ℕ → ℝ, (∀ m, 1 ≤ P m) ∧ ∀ (i : A.centers)
      {a : Finset Index} {z : ℝ} (hz : 0 < z), z ≤ 1 →
      ∀ hcover : (modeSupport (A.chartWeightCompact i) : Set SmallModes.Base) ⊆
        coverRegion a (z^6),
      ∀ (k : Index) (s : ℝ≥0), 0 < (s : ℝ) → s ≤ 1 →
      ∀ w : ℝ, 1 ≤ w → ∀ m,
      WeightedEstimates.WeightedBound univ s m (P m/z^(6*m))
        (w⁻¹ • A.exactCellCutoff i (pow_pos hz 6) hcover k) := by
  classical
  obtain ⟨C,hC,hcut⟩ := supported_normalized_cutoff_bounds
  let B := fun m => 1+∑ i : A.centers,
    supportedWeightedSeminorm (modeSupport (A.chartWeightCompact i)) 1 m (A.supportedPlaneWeight i)
  have hB (m : ℕ) : 1 ≤ B m := le_add_of_nonneg_right
    (Finset.sum_nonneg fun i _ => apply_nonneg _ _)
  have hb (i : A.centers) (m : ℕ) :
      WeightedEstimates.WeightedBound univ 1 m (B m) (A.supportedPlaneWeight i) := by
    apply (weightedBound_of_supportedSeminorm 1 m (A.supportedPlaneWeight i)).mono_const
    have hh : supportedWeightedSeminorm (modeSupport (A.chartWeightCompact i)) 1 m
        (A.supportedPlaneWeight i) ≤ ∑ j : A.centers,
          supportedWeightedSeminorm (modeSupport (A.chartWeightCompact j)) 1 m
            (A.supportedPlaneWeight j) :=
      Finset.single_le_sum (fun j _ => show 0 ≤
        supportedWeightedSeminorm (modeSupport (A.chartWeightCompact j)) 1 m
          (A.supportedPlaneWeight j) from apply_nonneg _ _) (Finset.mem_univ i)
    exact hh.trans (le_add_of_nonneg_left zero_le_one)
  refine ⟨fun m => C m*B m,fun m => one_le_mul_of_one_le_of_one_le (hC m) (hB m),?_⟩
  intro i a z hz hz1 hcover k s hs hs1 w hw m
  have hraw := (hcut (A.supportedPlaneWeight i) (pow_pos hz 6)
    (pow_le_one₀ hz.le hz1) hcover B (fun m => zero_le_one.trans (hB m)) (hb i) k m).shrink_scale
      s.coe_nonneg hs1
  have he : (A.exactCellCutoff i (pow_pos hz 6) hcover k : SmallModes.Base → ℝ) =
      supportedNormalizedCutoff (A.supportedPlaneWeight i) (pow_pos hz 6) hcover k := rfl
  have hraw' : WeightedEstimates.WeightedBound univ s m (C m*B m/z^(6*m))
      (A.exactCellCutoff i (pow_pos hz 6) hcover k) := by
    simpa only [he,pow_mul] using hraw
  have hbound : |w⁻¹| ≤ 1 := by
    rw [abs_of_nonneg (inv_nonneg.mpr (zero_le_one.trans hw))]
    exact inv_le_one_of_one_le₀ hw
  have hh := hraw'.const_smul uniqueDiffOn_univ
    (A.exactCellCutoff i (pow_pos hz 6) hcover k).contDiff.contDiffOn w⁻¹
  apply hh.mono_const
  simpa only [one_mul] using mul_le_mul_of_nonneg_right hbound
    (div_nonneg (mul_nonneg (zero_le_one.trans (hC m)) (zero_le_one.trans (hB m)))
      (pow_nonneg hz.le _))

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
