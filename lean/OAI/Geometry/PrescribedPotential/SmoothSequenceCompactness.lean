import Mathlib
import OAI.Geometry.PrescribedPotential.CircleRadialCalculus
import OAI.Geometry.PrescribedPotential.EvenRellich
import OAI.Geometry.PrescribedPotential.GlobalSmooth
import OAI.Geometry.PrescribedPotential.PatchCutoffs

namespace OAI

/-! Smooth Sequence Compactness. -/

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

lemma lower_tendsto_smooth {s t : ℝ} (hst : t ≤ s) (f : ℕ → Smooth A)
    (u : D.Sobolev s) (hf : Tendsto (fun n => D.embed s (f n)) atTop (𝓝 u)) :
    Tendsto (fun n => D.embed t (f n)) atTop (𝓝 (D.lower s t u)) := by
  have hh := (D.lower s t).continuous.tendsto u |>.comp hf
  simpa only [Function.comp_def,D.lower_embed hst] using hh

end Localizers
namespace GluingData
variable {g : KaehlerMetric A} (D : GluingData g ι)

lemma even_tower_subsequence (f : ℕ → Smooth A)
    (hbound : ∀ k : ℕ, ∃ C : ℝ, ∀ n : ℕ,
      ‖D.localizers.embed (((2*k : ℕ) : ℝ)+2) (f n)‖ ≤ C) :
    ∃ (u : ∀ k : ℕ, D.localizers.Sobolev ((2*k : ℕ) : ℝ)) (r : ℕ → ℕ),
      StrictMono r ∧ ∀ k : ℕ,
        Tendsto (fun n => D.localizers.embed ((2*k : ℕ) : ℝ) (f (r n))) atTop (𝓝 (u k)) := by
  choose C hC using hbound
  let K (k : ℕ) : Set (D.localizers.Sobolev ((2*k : ℕ) : ℝ)) :=
    closure (D.localizers.lower (((2*k : ℕ) : ℝ)+2) ((2*k : ℕ) : ℝ) ''
      Metric.closedBall 0 (C k))
  have hK (k : ℕ) : IsCompact (K k) :=
    (D.lower_even_compact k).isCompact_closure_image_closedBall (C k)
  have hf (n : ℕ) : (fun k : ℕ => D.localizers.embed ((2*k : ℕ) : ℝ) (f n)) ∈
      {x | ∀ k, x k ∈ K k} := by
    intro k
    apply subset_closure
    refine ⟨D.localizers.embed (((2*k : ℕ) : ℝ)+2) (f n),?_,?_⟩
    · simpa only [Metric.mem_closedBall,dist_zero_right] using hC k n
    · exact D.localizers.lower_embed (by linarith : ((2*k : ℕ) : ℝ) ≤ ((2*k : ℕ) : ℝ)+2) (f n)
  obtain ⟨u,_,r,hr,hu⟩ := (isCompact_pi_infinite hK).tendsto_subseq hf
  refine ⟨u,r,hr,fun k => ?_⟩
  exact (continuous_apply k).tendsto u |>.comp hu

 

theorem smooth_sequence_compact (f : ℕ → Smooth A)
    (hbound : ∀ k : ℕ, ∃ C : ℝ, ∀ n : ℕ,
      ‖D.localizers.embed (((2*k : ℕ) : ℝ)+2) (f n)‖ ≤ C) :
    ∃ (fLim : Smooth A) (r : ℕ → ℕ), StrictMono r ∧ ∀ k : ℕ,
      Tendsto (fun n => D.localizers.embed (k : ℝ) (f (r n))) atTop
        (𝓝 (D.localizers.embed (k : ℝ) fLim)) := by
  obtain ⟨u,r,hr,hu⟩ := D.even_tower_subsequence f hbound
  let u₀ := D.localizers.lower ((2*0 : ℕ) : ℝ) 0 (u 0)
  have h₀ : Tendsto (fun n => D.localizers.embed 0 (f (r n))) atTop (𝓝 u₀) :=
    D.localizers.lower_tendsto_smooth (Nat.cast_nonneg _) (fun n => f (r n)) (u 0) (hu 0)
  let v (k : ℕ) := D.localizers.lower ((2*k : ℕ) : ℝ) (k : ℝ) (u k)
  have hv (k : ℕ) : Tendsto (fun n => D.localizers.embed (k : ℝ) (f (r n))) atTop (𝓝 (v k)) :=
    D.localizers.lower_tendsto_smooth (by exact_mod_cast (show k ≤ 2*k by omega))
      (fun n => f (r n)) (u k) (hu k)
  have hv₀ (k : ℕ) : D.localizers.lower (k : ℝ) 0 (v k) = u₀ := by
    exact tendsto_nhds_unique
      (D.localizers.lower_tendsto_smooth (Nat.cast_nonneg k) (fun n => f (r n)) (v k) (hv k)) h₀
  obtain ⟨fLim,hfLim⟩ := D.allRegular_smooth (fun k => ⟨v k,hv₀ k⟩)
  refine ⟨fLim,r,hr,fun k => ?_⟩
  have he : v k = D.localizers.embed (k : ℝ) fLim := by
    apply D.localizers.lower_injective (Nat.cast_nonneg k)
    rw [hv₀,D.localizers.lower_embed (Nat.cast_nonneg k),hfLim]
  exact he ▸ hv k

end GluingData
end GlobalElliptic

end
end

end OAI
