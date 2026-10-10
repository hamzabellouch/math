import Mathlib
import OAI.Geometry.PrescribedPotential.GlobalStrongEmbedding
import OAI.Geometry.PrescribedPotential.PatchCutoffs
import OAI.Geometry.PrescribedPotential.RealSobolev
import OAI.Geometry.PrescribedPotential.SmoothSequenceCompactness

namespace OAI

/-! Real Smooth Compactness. -/

section

 

noncomputable section
open Set Filter Topology
open scoped ContDiff Classical
namespace GlobalElliptic
open Anticanonical SourceSmooth EllipticKernel SobolevChart
variable {d : ℕ} {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  {A : ComplexAtlas d X} {ι : Type*} [Fintype ι]
namespace Localizers
variable (D : Localizers A ι)

lemma smooth_tendsto_real_order (f : ℕ → Smooth A) (fLim : Smooth A)
    (hf : ∀ k : ℕ, Tendsto (fun n => D.embed (k : ℝ) (f n)) atTop
      (𝓝 (D.embed (k : ℝ) fLim))) (s : ℝ) :
    Tendsto (fun n => D.embed s (f n)) atTop (𝓝 (D.embed s fLim)) := by
  obtain ⟨k,hk⟩ := exists_nat_ge s
  have hh := D.lower_tendsto_smooth hk f (D.embed (k : ℝ) fLim) (hf k)
  simpa only [D.lower_embed hk] using hh

lemma smooth_value_tendsto (s : ℝ) (hs : (Module.finrank ℝ (EC d) : ℝ) < 2*s)
    (f : ℕ → Smooth A) (fLim : Smooth A)
    (hf : Tendsto (fun n => D.embed s (f n)) atTop (𝓝 (D.embed s fLim))) (x : X) :
    Tendsto (fun n => f n x) atTop (𝓝 (fLim x)) := by
  have hc : Continuous (fun u : D.Sobolev s => D.strong s u x) :=
    (D.strong s).continuous.eval continuous_const
  have ht := (hc.tendsto (D.embed s fLim)).comp hf
  simpa only [Function.comp_def,D.strong_embed s hs,Smooth.bounded,
    BoundedContinuousFunction.mkOfCompact_apply,ContinuousMap.coe_mk] using ht

lemma smooth_limit_real (f : ℕ → RealSmooth A) (fLim : Smooth A)
    (hf : ∀ s : ℝ, Tendsto (fun n => D.embed s (f n).val) atTop
      (𝓝 (D.embed s fLim))) : ∀ x, (fLim x).im = 0 := by
  intro x
  let s : ℝ := (Module.finrank ℝ (EC d) : ℝ)+1
  have hs : (Module.finrank ℝ (EC d) : ℝ) < 2*s := by
    dsimp only [s]
    linarith [Nat.cast_nonneg (α := ℝ) (Module.finrank ℝ (EC d))]
  have hv := D.smooth_value_tendsto s hs (fun n => (f n).val) fLim (hf s) x
  have hh := (Complex.continuous_im.tendsto (fLim x)).comp hv
  have he : (fun n => ((f n).val x).im) = (fun _ : ℕ => (0 : ℝ)) :=
    funext (fun n => (f n).property x)
  change Tendsto (fun n => ((f n).val x).im) atTop (𝓝 (fLim x).im) at hh
  rw [he] at hh
  exact tendsto_nhds_unique hh tendsto_const_nhds

end Localizers
namespace GluingData
variable {g : KaehlerMetric A} (D : GluingData g ι)

 

theorem real_smooth_sequence_compact (f : ℕ → RealSmooth A)
    (hbound : ∀ k : ℕ, ∃ C : ℝ, ∀ n : ℕ,
      ‖D.localizers.embed (((2*k : ℕ) : ℝ)+2) (f n).val‖ ≤ C) :
    ∃ (fLim : RealSmooth A) (r : ℕ → ℕ), StrictMono r ∧ ∀ s : ℝ,
      Tendsto (fun n => D.localizers.embed s (f (r n)).val) atTop
        (𝓝 (D.localizers.embed s fLim.val)) := by
  obtain ⟨fLim,r,hr,hf⟩ := D.smooth_sequence_compact (fun n => (f n).val) hbound
  have hf' := D.localizers.smooth_tendsto_real_order (fun n => (f (r n)).val) fLim hf
  exact ⟨⟨fLim,D.localizers.smooth_limit_real (fun n => f (r n)) fLim hf'⟩,r,hr,hf'⟩

end GluingData
end GlobalElliptic

end
end

end OAI
