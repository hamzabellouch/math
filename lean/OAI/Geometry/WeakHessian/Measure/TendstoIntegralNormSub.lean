import Mathlib

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile0
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported
open scoped ENNReal NNReal Topology BoundedContinuousFunction
open scoped NNReal
open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open MeasureTheory
open scoped ENNReal InnerProductSpace ComplexConjugate
open Set Filter
open scoped Topology ENNReal NNReal
open Set
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology ENNReal NNReal InnerProductSpace
open scoped BoundedContinuousFunction
open Set MeasureTheory Filter
open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory
open Set Filter Topology Bornology
open scoped InnerProductSpace
open Filter
open scoped Topology
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

attribute [local instance] Classical.propDecidable
namespace WeakHessian
open MeasureTheory Filter
open scoped Topology

variable {X : Type*} [MeasurableSpace X] {m : Measure X}

lemma tendsto_integral_norm_sub_of_nonneg_mass {ι : Type*} {l : Filter ι}
    [l.IsCountablyGenerated] {fs : ι → Lp ℝ 2 m} {f : Lp ℝ 2 m}
    (hf : Tendsto fs l (𝓝 f)) (hpos : ∀ i, ∀ᵐ x ∂m, 0 ≤ fs i x)
    (hfpos : ∀ᵐ x ∂m, 0 ≤ f x) (hi : ∀ i, Integrable (fs i) m)
    (hfi : Integrable f m)
    (hmass : Tendsto (fun i => ∫ x,fs i x ∂m) l (𝓝 (∫ x,f x ∂m))) :
    Tendsto (fun i => ∫ x, ‖fs i x-f x‖ ∂m) l (𝓝 0) := by
  apply tendsto_of_subseq_tendsto
  intro ns hns
  obtain ⟨ms,hms,hae⟩ := (tendstoInMeasure_of_tendsto_Lp (hf.comp hns)).exists_seq_tendsto_ae
  refine ⟨ms,?_⟩
  have hmin : Tendsto (fun n => ∫ x,min (fs (ns (ms n)) x) (f x) ∂m) atTop (𝓝 (∫ x,f x ∂m)) := by
    apply tendsto_integral_of_dominated_convergence (fun x => f x)
    · intro n
      exact (Lp.aestronglyMeasurable (fs (ns (ms n)))).inf (Lp.aestronglyMeasurable f)
    · exact hfi
    · intro n
      filter_upwards [hpos (ns (ms n)),hfpos] with x hx hy
      rw [Real.norm_eq_abs, abs_of_nonneg (le_min hx hy)]
      exact min_le_right _ _
    · filter_upwards [hae] with x hx
      simpa only [min_self,Function.comp_def] using hx.min (tendsto_const_nhds (x := f x))
  have he (n : ℕ) : (∫ x,‖fs (ns (ms n)) x-f x‖ ∂m) =
      (∫ x,fs (ns (ms n)) x ∂m)+(∫ x,f x ∂m)-2*(∫ x,min (fs (ns (ms n)) x) (f x) ∂m) := by
    have him : Integrable (fun x => min (fs (ns (ms n)) x) (f x)) m := (hi (ns (ms n))).inf hfi
    calc
      _ = ∫ x, (fs (ns (ms n)) x+f x)-2*min (fs (ns (ms n)) x) (f x) ∂m := by
        apply integral_congr_ae
        exact ae_of_all _ fun x => by
          dsimp only
          rw [Real.norm_eq_abs]
          rcases le_total (fs (ns (ms n)) x) (f x) with h|h
          · rw [min_eq_left h,abs_of_nonpos (sub_nonpos.mpr h)]; ring
          · rw [min_eq_right h,abs_of_nonneg (sub_nonneg.mpr h)]; ring
      _ = _ := by
        have h1 := integral_sub ((hi (ns (ms n))).add hfi) (him.const_mul 2)
        have h2 := integral_add (hi (ns (ms n))) hfi
        simpa only [Pi.add_apply,integral_const_mul,h2] using h1
  simp_rw [he]
  have H := ((hmass.comp (hns.comp hms.tendsto_atTop)).add (tendsto_const_nhds (x := ∫ x,f x ∂m))).sub (hmin.const_mul 2)
  have hz : (∫ x,f x ∂m)+(∫ x,f x ∂m)-2*(∫ x,f x ∂m) = 0 := by ring
  rw [hz] at H
  simpa only [Function.comp_def] using H
end WeakHessian

end
end InlinedFile0

end OAI
