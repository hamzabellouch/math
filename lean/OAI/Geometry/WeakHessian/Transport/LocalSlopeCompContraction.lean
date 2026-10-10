import Mathlib
import OAI.Geometry.WeakHessian.LocalBounds.SlopeApprox
import OAI.Geometry.WeakHessian.Sobolev.CheegerEnergyCongrAe

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile0
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open Set Filter Topology Bornology
open scoped InnerProductSpace

attribute [local instance] Classical.propDecidable
open Set
open scoped NNReal
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

namespace WeakHessian
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] {m : Measure X}

omit [MeasurableSpace X] in
lemma localSlope_comp_contraction {η : ℝ → ℝ} (hη : LipschitzWith 1 η)
    (f : X → ℝ) (x : X) : localSlope (η ∘ f) x ≤ localSlope f x := by
  simp only [localSlope_eq_iInf_slopeApprox]
  apply iInf_mono
  intro n
  unfold slopeApprox
  apply iSup_mono
  intro y
  apply iSup_mono
  intro _
  apply ENNReal.ofReal_le_ofReal
  apply div_le_div_of_nonneg_right _ dist_nonneg
  simpa only [Function.comp_apply, Real.dist_eq, NNReal.coe_one, one_mul] using hη.dist_le_mul (f y) (f x)

lemma cheegerEnergy_normalContraction {η : ℝ → ℝ} (hη : LipschitzWith 1 η)
    (hη0 : η 0 = 0) (f : X → ℝ) :
    cheegerEnergy m (η ∘ f) ≤ cheegerEnergy m f := by
  classical
  by_cases hf : MemLp f 2 m
  · change cheegerEnergy m (η ∘ f) ≤ (if MemLp f 2 m then _ else ∞)
    rw [ite_eq_left hf]
    apply le_sInf
    rintro a ⟨fs, hfs, hc, rfl⟩
    have hφ : MemLp (η ∘ f) 2 m := hη.comp_memLp hη0 hf
    have hφs : ∀ n, GloballyLipschitz (η ∘ fs n) ∧ MemLp (η ∘ fs n) 2 m := by
      intro n
      obtain ⟨L, hL⟩ := (hfs n).1
      exact ⟨⟨_, hη.comp hL⟩, hη.comp_memLp hη0 (hfs n).2⟩
    have hcφ : Tendsto (fun n => eLpNorm (fun x => η (fs n x)-η (f x)) 2 m) atTop (𝓝 0) := by
      apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hc (fun _ => bot_le)
      intro n
      apply eLpNorm_mono ((hφs n).2.aestronglyMeasurable.sub hφ.aestronglyMeasurable)
      intro x
      simpa only [Pi.sub_apply, Function.comp_apply, Real.norm_eq_abs, Real.dist_eq,
        NNReal.coe_one, one_mul] using
        hη.dist_le_mul (fs n x) (f x)
    apply (cheegerEnergy_le_liminf hφ hφs hcφ).trans
    refine liminf_le_liminf (Eventually.of_forall fun n => ?_)
    apply mul_le_mul_right
    apply lintegral_mono
    intro x
    exact pow_le_pow_left' (localSlope_comp_contraction hη (fs n) x) 2
  · simp only [cheegerEnergy, ite_eq_right hf, le_top]

end WeakHessian

end
end InlinedFile0

end OAI
