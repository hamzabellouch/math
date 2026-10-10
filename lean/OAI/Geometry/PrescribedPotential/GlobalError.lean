import Mathlib
import OAI.Geometry.PrescribedPotential.GlobalParametrixEquation

namespace OAI

/-! Global Error. -/

section

 
noncomputable section
open Set Filter Topology _root_.MeasureTheory _root_.OAI.MeasureTheory
open scoped SchwartzMap ContDiff Classical ComplexOrder MatrixOrder
namespace GlobalElliptic
open Anticanonical SourceSmooth EllipticKernel SobolevChart MetricLocalization
variable {d : ℕ} {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  {A : ComplexAtlas d X} {ι : Type*} [Fintype ι]
namespace GluingData
variable {g : KaehlerMetric A} (D : GluingData g ι)

lemma error_piece_bound (p : ι) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ m (hm : 1 ≤ m) (f : Smooth A),
      ‖D.localizers.embed 0 (globalize (D.patch p).index (D.outerCutoff p)
        ((D.patch p).cutoffError (D.cutoff p).val
          ((D.patch p).localInverse m hm (D.forcing p f))))‖ ≤
        C / m * ‖D.localizers.embed 0 f‖ := by
  obtain ⟨B, hB, hb⟩ := globalize_integer_bound D.localizers (D.patch p).index (D.outerCutoff p) 0
  let c := cutoffErrorConstant (D.patch p).matrix (D.patch p).positive
    (coefficientBCF (D.patch p).coefficient) (D.cutoff p).val
  refine ⟨B * |c|, mul_nonneg hB (abs_nonneg _), fun m hm f => ?_⟩
  have hm0 : 0 ≤ m := le_trans (by norm_num) hm
  have hb' := hb ((D.patch p).cutoffError (D.cutoff p).val
    ((D.patch p).localInverse m hm (D.forcing p f)))
  rw [Nat.cast_zero] at hb'
  apply hb'.trans
  calc
    _ ≤ B * (c / m * ‖schwartzCoord 0 (D.forcing p f)‖) :=
      mul_le_mul_of_nonneg_left ((D.patch p).cutoffError_bound m hm (D.cutoff p).val (D.forcing p f)) hB
    _ ≤ B * (|c| / m * ‖D.localizers.embed 0 f‖) := by
      apply mul_le_mul_of_nonneg_left _ hB
      exact mul_le_mul (div_le_div_of_nonneg_right (le_abs_self _) hm0)
        (D.forcing_bound p 0 f) (norm_nonneg _) (div_nonneg (abs_nonneg _) hm0)
    _ = _ := by ring

 
theorem error_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ m (hm : 1 ≤ m) (f : Smooth A),
      ‖D.localizers.embed 0 (D.error m hm f)‖ ≤ C / m * ‖D.localizers.embed 0 f‖ := by
  choose C hC hc using D.error_piece_bound
  refine ⟨∑ p, C p, Finset.sum_nonneg (fun p _ => hC p), fun m hm f => ?_⟩
  rw [error_apply, map_sum, Finset.sum_div, Finset.sum_mul]
  exact (norm_sum_le _ _).trans (Finset.sum_le_sum (fun p _ => hc p m hm f))

 

theorem exists_contractive_shift :
    ∃ m : ℝ, ∃ hm : 1 ≤ m, ∃ q : ℝ, 0 ≤ q ∧ q < 1 ∧
      ∀ f : Smooth A, ‖D.localizers.embed 0 (D.error m hm f)‖ ≤ q * ‖D.localizers.embed 0 f‖ := by
  obtain ⟨C, hC, hc⟩ := D.error_bound
  have hm : 1 ≤ C + 1 := by linarith
  refine ⟨C + 1, hm, C / (C + 1), div_nonneg hC (by linarith), ?_, hc _ hm⟩
  exact (div_lt_one (by linarith : 0 < C + 1)).mpr (by linarith)

end GluingData
end GlobalElliptic

end
end

end OAI
