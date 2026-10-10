import Mathlib
import OAI.Geometry.PrescribedPotential.CompletedResolvent
import OAI.Geometry.PrescribedPotential.GlobalCompletion

namespace OAI

/-! Fredholm Regularity. -/

section

 

noncomputable section
open Set Filter Topology _root_.MeasureTheory _root_.OAI.MeasureTheory
open scoped SchwartzMap ContDiff Classical
namespace GlobalElliptic
open Anticanonical SourceSmooth EllipticKernel SobolevChart
variable {d : ℕ} {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  {A : ComplexAtlas d X} {ι : Type*} [Fintype ι]
namespace Localizers
variable {D : Localizers A ι}

lemma BoundedCore.add {s t : ℝ} {S T : Smooth A →ₗ[ℝ] Smooth A}
    (hS : D.BoundedCore s t S) (hT : D.BoundedCore s t T) :
    D.BoundedCore s t (S+T) := by
  obtain ⟨B, hB, hb⟩ := hS
  obtain ⟨C, hC, hc⟩ := hT
  refine ⟨B+C, add_nonneg hB hC, fun f => ?_⟩
  simp only [LinearMap.add_apply, map_add]
  exact (norm_add_le _ _).trans (by simpa only [add_mul] using add_le_add (hb f) (hc f))

lemma BoundedCore.smul {s t : ℝ} {T : Smooth A →ₗ[ℝ] Smooth A}
    (hT : D.BoundedCore s t T) (c : ℝ) : D.BoundedCore s t (c • T) := by
  obtain ⟨C, hC, hc⟩ := hT
  refine ⟨‖c‖*C, mul_nonneg (norm_nonneg _) hC, fun f => ?_⟩
  simp only [LinearMap.smul_apply, map_smul, norm_smul, mul_assoc]
  exact mul_le_mul_of_nonneg_left (hc f) (norm_nonneg c)

lemma extendCore_add {s t : ℝ} {S T : Smooth A →ₗ[ℝ] Smooth A}
    (hS : D.BoundedCore s t S) (hT : D.BoundedCore s t T) :
    D.extendCore s t (S+T) = D.extendCore s t S + D.extendCore s t T := by
  apply DFunLike.coe_injective
  apply (D.embed_dense s).equalizer (by fun_prop) (by fun_prop)
  funext f
  simp only [Function.comp_apply, _root_.add_apply, D.extendCore_embed hS,
    D.extendCore_embed hT, D.extendCore_embed (hS.add hT), LinearMap.add_apply, map_add]

lemma extendCore_smul {s t : ℝ} {T : Smooth A →ₗ[ℝ] Smooth A}
    (hT : D.BoundedCore s t T) (c : ℝ) :
    D.extendCore s t (c • T) = c • D.extendCore s t T := by
  apply DFunLike.coe_injective
  apply (D.embed_dense s).equalizer (by fun_prop) (by fun_prop)
  funext f
  simp only [Function.comp_apply, _root_.smul_apply, D.extendCore_embed hT,
    D.extendCore_embed (hT.smul c), LinearMap.smul_apply, map_smul]

end Localizers
namespace GluingData
variable {g : KaehlerMetric A} (D : GluingData g ι)

def resolventZero (m : ℝ) (hm : 1 ≤ m) (he : ‖D.completedError m hm‖ < 1) :
    D.localizers.Sobolev 0 →L[ℝ] D.localizers.Sobolev 0 :=
  D.localizers.lower 2 0 ∘L D.completedResolvent m hm he

def feedbackCore (m : ℝ) (hm : 1 ≤ m) : Smooth A →ₗ[ℝ] Smooth A :=
  D.error m hm + (m^2 : ℝ) • D.parametrix m hm

lemma feedbackCore_bound (m : ℝ) (hm : 1 ≤ m) (k : ℕ) :
    D.localizers.BoundedCore (k : ℝ) ((k : ℝ)+1) (D.feedbackCore m hm) := by
  have hQ : D.localizers.BoundedCore (k : ℝ) ((k : ℝ)+2) (D.parametrix m hm) :=
    D.parametrix_bound m hm k
  exact (D.error_bound_integer m hm k).add ((hQ.target_mono (by linarith)).smul (m^2))

lemma feedbackCore_bound_zero (m : ℝ) (hm : 1 ≤ m) :
    D.localizers.BoundedCore 0 0 (D.feedbackCore m hm) := by
  have hb := D.feedbackCore_bound m hm 0
  rw [Nat.cast_zero, zero_add] at hb
  exact hb.target_mono (by norm_num)

lemma completed_feedback (m : ℝ) (hm : 1 ≤ m) (v : D.localizers.Sobolev 0) :
    D.localizers.extendCore 0 0 (D.feedbackCore m hm) v =
      D.completedError m hm v + (m^2 : ℝ) •
        D.localizers.lower 2 0 (D.completedParametrix m hm v) := by
  have hQ := (D.completedParametrix_bound m hm).target_mono (by norm_num : (0:ℝ) ≤ 2)
  rw [feedbackCore, Localizers.extendCore_add (D.error_bound_zero m hm) (hQ.smul (m^2)),
    Localizers.extendCore_smul hQ]
  simp only [_root_.add_apply, _root_.smul_apply]
  change _ = (D.localizers.extendCore 0 0 (D.error m hm)) v + (m^2 : ℝ) •
    D.localizers.lower 2 0 (D.localizers.extendCore 0 2 (D.parametrix m hm) v)
  rw [D.localizers.lower_extendCore (by norm_num : (0:ℝ) ≤ 2) _
    (D.completedParametrix_bound m hm) hQ v]

 

theorem resolvent_feedback_regular (m : ℝ) (hm : 1 ≤ m)
    (he : ‖D.completedError m hm‖ < 1) (w : D.localizers.Sobolev 0)
    (f : Smooth A) (hw : w = D.localizers.embed 0 f + (m^2 : ℝ) • D.resolventZero m hm he w) :
    D.localizers.AllRegular (D.resolventZero m hm he w) := by
  let v := D.errorInverse m hm he w
  have hv : v - D.completedError m hm v =
      D.localizers.embed 0 f + (m^2 : ℝ) •
        D.localizers.lower 2 0 (D.completedParametrix m hm v) :=
    (D.errorInverse_equation m hm he w).trans hw
  have hvreg : D.localizers.AllRegular v := by
    apply D.localizers.allRegular_of_gain (D.feedbackCore m hm)
      (D.feedbackCore_bound_zero m hm) (D.feedbackCore_bound m hm) f
    rw [D.completed_feedback]
    calc
      v = D.localizers.embed 0 f + (m^2 : ℝ) •
          D.localizers.lower 2 0 (D.completedParametrix m hm v) +
          D.completedError m hm v := sub_eq_iff_eq_add.mp hv
      _ = _ := by abel
  exact D.parametrix_regular m hm v hvreg

lemma smooth_shifted_equation (m : ℝ) (hm : 1 ≤ m)
    (he : ‖D.completedError m hm‖ < 1) (w : D.localizers.Sobolev 0)
    (u : Smooth A) (hu : D.localizers.embed 0 u = D.resolventZero m hm he w) :
    D.localizers.embed 0 ((m^2 : ℝ) • u - complexL g u) = w := by
  have h2 : D.localizers.embed 2 u = D.completedResolvent m hm he w := by
    apply D.localizers.lower_injective (by norm_num : (0 : ℝ) ≤ 2)
    rw [D.localizers.lower_embed (by norm_num : (0 : ℝ) ≤ 2)]
    exact hu
  have h := D.completedResolvent_equation m hm he w
  rw [← h2] at h
  simpa only [shiftedOperator, completedL, _root_.sub_apply,
    _root_.smul_apply, D.localizers.lower_embed (by norm_num : (0 : ℝ) ≤ 2),
    D.localizers.extendCore_embed D.complexL_bound, map_sub, map_smul] using h

end GluingData
end GlobalElliptic

end
end

end OAI
