import Mathlib
import OAI.Geometry.WeakHessian.LocalBounds.TriangularFold

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
open scoped Topology ENNReal NNReal

lemma triangularFold_norm_le (δ x : ℝ) : ‖triangularFold δ x‖ ≤ ‖x‖ := by
  have H := (triangularFold_lipschitz δ).norm_sub_le x 0
  simpa only [triangularFold_zero, sub_zero, NNReal.coe_one, one_mul] using H

lemma triangularFold_tendsto (x : ℝ) :
    Tendsto (fun n : ℕ => triangularFold (1/((n:ℝ)+1)) x) atTop (𝓝 0) := by
  apply squeeze_zero (fun _ => triangularFold_nonneg _ _)
    (fun n => triangularFold_le (by positivity) x)
  have H : Tendsto (fun n : ℕ => (1:ℝ)/((n:ℝ)+1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  simpa only [zero_div, one_div] using H.div_const 2

variable {X : Type*} [MeasurableSpace X] {m : Measure X}

lemma triangularFold_tendsto_Lp (f : Lp ℝ 2 m) :
    Tendsto (fun n : ℕ => (triangularFold_lipschitz (1/((n:ℝ)+1))).compLp
      (triangularFold_zero _) f) atTop (𝓝 0) := by
  let g : ℕ → X → ℝ := fun n x => triangularFold (1/((n:ℝ)+1)) (f x)
  have hg (n : ℕ) : MemLp (g n) 2 m :=
    (triangularFold_lipschitz _).comp_memLp (triangularFold_zero _) (Lp.memLp f)
  have hi : UnifIntegrable g 2 m := by
    apply unifIntegrable_iff'.mpr
    intro ε hε
    obtain ⟨δ,hδ,hδf⟩ := (Lp.memLp f).eLpNorm_indicator_le (by norm_num) (by norm_num) hε
    refine ⟨δ,hδ,fun n s hs hms => ?_⟩
    rw [← eLpNorm_indicator_eq_eLpNorm_restrict hs]
    apply le_trans (eLpNorm_mono ((hg n).aestronglyMeasurable.indicator hs) (fun x => ?_))
      (hδf s hs hms)
    by_cases hx : x ∈ s
    · simpa only [Set.indicator_of_mem hx,g] using triangularFold_norm_le (1/((n:ℝ)+1)) (f x)
    · simp only [Set.indicator_of_notMem hx,le_refl]
  have ht : UnifTight g 2 m := by
    intro ε hε
    obtain ⟨s,hsm,hs,hfs⟩ := UnifTight.exists_measurableSet_indicator
      (unifTight_const (ι := ℕ) (by norm_num) (Lp.memLp f)) hε.ne'
    refine ⟨s,hs.ne,fun n => ?_⟩
    apply le_trans (eLpNorm_mono ((hg n).aestronglyMeasurable.indicator hsm.compl)
      (fun x => ?_)) (hfs n)
    by_cases hx : x ∈ sᶜ
    · simpa only [Set.indicator_of_mem hx,g] using triangularFold_norm_le (1/((n:ℝ)+1)) (f x)
    · simp only [Set.indicator_of_notMem hx,le_refl]
  have hconv := tendsto_Lp_of_tendsto_ae (by norm_num : (1:ℝ≥0∞) ≤ 2)
    (by norm_num : (2:ℝ≥0∞) ≠ ∞) (fun index => (hg index).aestronglyMeasurable)
      (MemLp.zero (α := X) (ε := ℝ))
      hi ht (Eventually.of_forall fun x => triangularFold_tendsto (f x))
  rw [Lp.tendsto_Lp_iff_tendsto_eLpNorm']
  convert hconv using 1
  ext n
  apply eLpNorm_congr_ae
  filter_upwards [(triangularFold_lipschitz (1/((n:ℝ)+1))).coeFn_compLp
      (triangularFold_zero _) f, Lp.coeFn_zero ℝ 2 m] with x hx hz
  simp only [Pi.sub_apply, hx, hz, Pi.zero_apply, sub_zero, Function.comp_apply, g]

lemma triangularFold_tendsto_toLp {f : X → ℝ} (hf : MemLp f 2 m) :
    Tendsto (fun n : ℕ => ((triangularFold_lipschitz (1/((n:ℝ)+1))).comp_memLp
      (triangularFold_zero _) hf).toLp (triangularFold (1/((n:ℝ)+1)) ∘ f)) atTop (𝓝 0) := by
  have he (n : ℕ) : ((triangularFold_lipschitz (1/((n:ℝ)+1))).comp_memLp
        (triangularFold_zero _) hf).toLp (triangularFold (1/((n:ℝ)+1)) ∘ f) =
      (triangularFold_lipschitz (1/((n:ℝ)+1))).compLp (triangularFold_zero _) (hf.toLp f) := by
    apply Lp.ext
    filter_upwards [((triangularFold_lipschitz (1/((n:ℝ)+1))).comp_memLp
      (triangularFold_zero _) hf).coeFn_toLp,
      (triangularFold_lipschitz (1/((n:ℝ)+1))).coeFn_compLp (triangularFold_zero _) (hf.toLp f),
      hf.coeFn_toLp] with x h1 h2 h3
    simp only [h1,h2,Function.comp_apply,h3]
  simpa only [he] using triangularFold_tendsto_Lp (hf.toLp f)

end WeakHessian

end
end InlinedFile0

end OAI
