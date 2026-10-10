import OAI.Geometry.NodalSets.Elliptic.RealCubeCellPartition
import OAI.Geometry.NodalSets.Elliptic.RealScaledCubePoincare

namespace OAI

namespace Yau.Geometry
open Yau.Jets MeasureTheory Set Function
open scoped ContDiff
noncomputable section

def realCubeCellMean (W : Yau.Jets.Coord → ℝ) (n : ℕ) (k : Fin 4 → Fin n) : ℝ :=
  (∫ x in realCubeCell n k, W x)/(2/(n:ℝ))^4

lemma realCubeCell_poincare {n : ℕ} (hn : 0 < n) (k : Fin 4 → Fin n)
    (W : Yau.Jets.Coord → ℝ) (hW : ContDiff ℝ ∞ W) :
    (∫ x in realCubeCell n k, (W x-realCubeCellMean W n k)^2) ≤
      (4/(n:ℝ)^2)*(∫ x in realCubeCell n k, ∑ i, (Yau.coordPartial W x i)^2) := by
  have hnR : (0:ℝ)<n := by exact_mod_cast hn
  have h := real_scaledCube_poincare 4 (corrugationCubeCenter (fun _ ↦ -1) 2 n k)
    (div_pos zero_lt_one hnR) W hW
  simpa only [realCubeCell,realCubeCellMean,mul_one_div,div_pow,one_pow,mul_one_div] using h

theorem realCubeCell_total_error {n : ℕ} (hn : 0 < n)
    (W : Yau.Jets.Coord → ℝ) (hW : ContDiff ℝ ∞ W) :
    (∑ k : Fin 4 → Fin n, ∫ x in realCubeCell n k, (W x-realCubeCellMean W n k)^2) ≤
      (4/(n:ℝ)^2)*(∫ x in realFinCube 4, ∑ i, (Yau.coordPartial W x i)^2) := by
  have h := Finset.sum_le_sum (fun k (_ : k ∈ (Finset.univ : Finset (Fin 4 → Fin n))) ↦
    realCubeCell_poincare hn k W hW)
  rw [← Finset.mul_sum,← realCubeCell_integral_sum hn] at h
  · exact h
  · exact realFinCube_integrable 4 _
      (continuous_finsetSum _ (fun i _ ↦ (Yau.real_coordPartial_smooth W hW i).continuous.pow 2))

lemma realCubeCell_mean_square_le {n : ℕ} (hn : 0 < n) (k : Fin 4 → Fin n)
    (W : Yau.Jets.Coord → ℝ) (hW : Continuous W) :
    (2/(n:ℝ))^4*(realCubeCellMean W n k)^2 ≤ ∫ x in realCubeCell n k, W x^2 := by
  have hnR : (0:ℝ)<n := by exact_mod_cast hn
  let : IsFiniteMeasure (volume.restrict (realCubeCell n k)) :=
    isFiniteMeasure_restrict.mpr (realCubeCell_isCompact n k).measure_ne_top
  have h := real_mean_square_contraction (volume.restrict (realCubeCell n k))
    (by rw [realCubeCell_mass hn]; positivity) W
    (hW.continuousOn.integrableOn_compact (realCubeCell_isCompact n k))
    ((hW.pow 2).continuousOn.integrableOn_compact (realCubeCell_isCompact n k))
  simpa only [realCubeCell_mass hn,realCubeCellMean] using h

lemma realCubeCell_mean_bound {n : ℕ} (hn : 0 < n) (k : Fin 4 → Fin n)
    (W : Yau.Jets.Coord → ℝ) (hW : Continuous W) {C : ℝ} (hC : 0 ≤ C)
    (hbound : (∫ x in realFinCube 4, W x^2) ≤ C) :
    |realCubeCellMean W n k| ≤ C/(2/(n:ℝ))^4+1 := by
  have hnR : (0:ℝ)<n := by exact_mod_cast hn
  have hm : 0 < (2/(n:ℝ))^4 := by positivity
  have hi := setIntegral_mono_set (realFinCube_integrable 4 _ (hW.pow 2))
    (Filter.Eventually.of_forall (fun x ↦ sq_nonneg (W x)))
    (realCubeCell_subset hn k).eventuallyLE
  have hs := (realCubeCell_mean_square_le hn k W hW).trans (hi.trans hbound)
  have hs' : (realCubeCellMean W n k)^2 ≤ C/(2/(n:ℝ))^4 := by
    apply (le_div_iff₀ hm).mpr
    simpa only [mul_comm] using hs
  have hv : 0 ≤ C/(2/(n:ℝ))^4 := div_nonneg hC hm.le
  rw [abs_le]
  constructor <;> nlinarith [sq_nonneg (realCubeCellMean W n k-1),sq_nonneg (realCubeCellMean W n k+1)]

end
end Yau.Geometry

end OAI
