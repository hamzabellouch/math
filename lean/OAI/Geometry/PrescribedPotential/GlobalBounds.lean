import Mathlib
import OAI.Geometry.PrescribedPotential.CutoffHigher
import OAI.Geometry.PrescribedPotential.GlobalCompletion
import OAI.Geometry.PrescribedPotential.GlobalError
import OAI.Geometry.PrescribedPotential.GlobalParametrixEquation

namespace OAI

/-! Global Bounds. -/

section

 

noncomputable section
open Set Filter Topology _root_.MeasureTheory _root_.OAI.MeasureTheory TemperedDistribution LineDeriv
open scoped SchwartzMap ContDiff Classical BoundedContinuousFunction ComplexOrder MatrixOrder
namespace GlobalElliptic
open Anticanonical SourceSmooth EllipticKernel SobolevChart MetricLocalization
variable {d : ℕ} {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  {A : ComplexAtlas d X} {ι : Type*} [Fintype ι]
namespace Localizers
variable {D : Localizers A ι}

lemma BoundedCore.comp {s t r : ℝ} {S T : Smooth A →ₗ[ℝ] Smooth A}
    (hS : D.BoundedCore t r S) (hT : D.BoundedCore s t T) :
    D.BoundedCore s r (S.comp T) := by
  obtain ⟨C, hC, hc⟩ := hS
  obtain ⟨B, hB, hb⟩ := hT
  refine ⟨C * B, mul_nonneg hC hB, fun f => ?_⟩
  exact (hc (T f)).trans (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (hb f) hC)

lemma BoundedCore.source_mono {s t r : ℝ} {T : Smooth A →ₗ[ℝ] Smooth A}
    (hT : D.BoundedCore s t T) (hrs : s ≤ r) : D.BoundedCore r t T := by
  simpa only [LinearMap.comp_id] using hT.comp (D.boundedCore_lower hrs)

lemma BoundedCore.target_mono {s t r : ℝ} {T : Smooth A →ₗ[ℝ] Smooth A}
    (hT : D.BoundedCore s t T) (hrt : r ≤ t) : D.BoundedCore s r T := by
  simpa only [LinearMap.id_comp] using (D.boundedCore_lower hrt).comp hT
end Localizers

namespace GluingData
variable {g : KaehlerMetric A} (D : GluingData g ι)

lemma error_bound_zero (m : ℝ) (hm : 1 ≤ m) :
    D.localizers.BoundedCore 0 0 (D.error m hm) := by
  obtain ⟨C, hC, hc⟩ := D.error_bound
  exact ⟨C / m, div_nonneg hC (le_trans (by norm_num) hm), hc m hm⟩

lemma error_piece_bound_integer (m : ℝ) (hm : 1 ≤ m) (k : ℕ) (p : ι) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : Smooth A,
      ‖D.localizers.embed ((k : ℝ) + 1) (globalize (D.patch p).index (D.outerCutoff p)
        ((D.patch p).cutoffError (D.cutoff p).val
          ((D.patch p).localInverse m hm (D.forcing p f))))‖ ≤
        C * ‖D.localizers.embed (k : ℝ) f‖ := by
  obtain ⟨B, hB, hb⟩ := globalize_integer_bound D.localizers (D.patch p).index (D.outerCutoff p) (k + 1)
  have he : CoreBound ((k : ℝ) + 2) ((k : ℝ) + 1)
      ((D.patch p).cutoffError (D.cutoff p).val) := by
    convert schwartzCutoffError_bound_integer (D.patch p).coefficients
      (D.patch p).coefficients_temperate (D.cutoff p).val (k + 1) using 1 <;> push_cast <;> first | rfl | ring
  obtain ⟨C, hC, hc⟩ := he.comp ((D.patch p).localInverse_bound m hm k)
  refine ⟨B * C, mul_nonneg hB hC, fun f => ?_⟩
  have hh := hb ((D.patch p).cutoffError (D.cutoff p).val
    ((D.patch p).localInverse m hm (D.forcing p f)))
  rw [Nat.cast_add, Nat.cast_one] at hh
  apply hh.trans
  have hr := (hc (D.forcing p f)).trans
    (mul_le_mul_of_nonneg_left (D.forcing_bound p (k : ℝ) f) hC)
  simpa only [mul_assoc, Function.comp_apply, ParametrixPatch.differential] using mul_le_mul_of_nonneg_left hr hB

 
theorem error_bound_integer (m : ℝ) (hm : 1 ≤ m) (k : ℕ) :
    D.localizers.BoundedCore (k : ℝ) ((k : ℝ) + 1) (D.error m hm) := by
  choose C hC hc using D.error_piece_bound_integer m hm k
  refine ⟨∑ p, C p, Finset.sum_nonneg (fun p _ => hC p), fun f => ?_⟩
  rw [error_apply, map_sum, Finset.sum_mul]
  exact (norm_sum_le _ _).trans (Finset.sum_le_sum (fun p _ => hc p f))

lemma complexL_reconstruction (f : Smooth A) :
    complexL g f = ∑ p, globalize (D.patch p).index (D.outerCutoff p)
      ((D.patch p).differential (SchwartzMap.smulLeftCLM ℂ (D.cutoff p).val (D.forcing p f))) := by
  conv_lhs => rw [← D.forcing_reconstruction f, map_sum]
  apply Finset.sum_congr rfl
  intro p _
  exact complexL_globalize (D.patch p) (D.cutoff p) (D.outerCutoff p)
    (D.cutoff_support p) (D.outerCutoff_one p) _

lemma complexL_piece_bound (p : ι) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : Smooth A,
      ‖D.localizers.embed 0 (globalize (D.patch p).index (D.outerCutoff p)
        ((D.patch p).differential (SchwartzMap.smulLeftCLM ℂ (D.cutoff p).val (D.forcing p f))))‖ ≤
        C * ‖D.localizers.embed 2 f‖ := by
  obtain ⟨B, hB, hb⟩ := globalize_integer_bound D.localizers (D.patch p).index (D.outerCutoff p) 0
  have hk : CoreBound 2 2 (SchwartzMap.smulLeftCLM ℂ (D.cutoff p).val) :=
    coreBound_product_integer (D.cutoff p).val 2
  obtain ⟨C, hC, hc⟩ := (schwartzDifferential_bound (D.patch p).coefficients
    (D.patch p).coefficients_temperate).comp hk
  refine ⟨B * C, mul_nonneg hB hC, fun f => ?_⟩
  have hh := hb ((D.patch p).differential (SchwartzMap.smulLeftCLM ℂ (D.cutoff p).val (D.forcing p f)))
  rw [Nat.cast_zero] at hh
  apply hh.trans
  have hr := (hc (D.forcing p f)).trans
    (mul_le_mul_of_nonneg_left (D.forcing_bound p 2 f) hC)
  simpa only [mul_assoc, Function.comp_apply, ParametrixPatch.differential] using mul_le_mul_of_nonneg_left hr hB

 
theorem complexL_bound : D.localizers.BoundedCore 2 0 (complexL g) := by
  choose C hC hc using D.complexL_piece_bound
  refine ⟨∑ p, C p, Finset.sum_nonneg (fun p _ => hC p), fun f => ?_⟩
  rw [D.complexL_reconstruction, map_sum, Finset.sum_mul]
  exact (norm_sum_le _ _).trans (Finset.sum_le_sum (fun p _ => hc p f))

end GluingData
end GlobalElliptic

end
end

end OAI
