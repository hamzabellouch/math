import Mathlib
import OAI.Analysis.CoulombIonization.ThomasFermi.TfIncreasingData

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace Convolution
open Filter
open scoped Topology InnerProductSpace
open MeasureTheory Complex Filter
open scoped Topology InnerProductSpace
open MeasureTheory Complex Filter
open scoped Topology InnerProductSpace ContDiff
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace Convolution
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace ENNReal
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open Set Filter Topology InnerProductSpace Laplacian
open MeasureTheory Filter
open scoped Topology
open MeasureTheory Filter
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter
open scoped Topology BigOperators InnerProductSpace
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter
open scoped Topology BigOperators Pointwise
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open scoped Convolution
open scoped RealInnerProductSpace
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Set Filter Metric Topology InnerProductSpace Laplacian
open MeasureTheory Set Filter Metric Topology InnerProductSpace Laplacian
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
namespace CoulombAnalysis

def tfInfiniteField (x : TFSpace) : ℝ := tfInfiniteRadial ‖x‖

lemma tfInfinite_sqrt_hasDerivAt {s : ℝ} (hs : 0 < s) :
    HasDerivAt (fun t => tfInfiniteRadial (Real.sqrt t))
      (-tfInfiniteCharge (Real.sqrt s) / (2 * (Real.sqrt s)^3)) s := by
  have hh := (tfInfiniteRadial_hasDerivAt (Real.sqrt_pos.mpr hs)).comp s (Real.hasDerivAt_sqrt hs.ne')
  convert hh using 1 <;> (try rfl)
  unfold tfInfiniteSlope
  field_simp [Real.sqrt_ne_zero'.mpr hs]

lemma tfInfinite_sqrt_second {s : ℝ} (hs : 0 < s) :
    deriv (deriv (fun t => tfInfiniteRadial (Real.sqrt t))) s =
      CoulombPDE.reaction tfReactionCoefficient (tfInfiniteRadial (Real.sqrt s)) / (4 * (Real.sqrt s)^2) +
        3 * tfInfiniteCharge (Real.sqrt s) / (4 * (Real.sqrt s)^5) := by
  have he : deriv (fun t => tfInfiniteRadial (Real.sqrt t)) =ᶠ[𝓝 s]
      fun t => -tfInfiniteCharge (Real.sqrt t) / (2 * (Real.sqrt t)^3) := by
    filter_upwards [Ioi_mem_nhds hs] with t ht
    exact (tfInfinite_sqrt_hasDerivAt ht).deriv
  rw [he.deriv_eq]
  have hm := (tfInfiniteCharge_hasDerivAt (Real.sqrt_pos.mpr hs)).comp s (Real.hasDerivAt_sqrt hs.ne')
  have ht := ((Real.hasDerivAt_sqrt hs.ne').pow 3).const_mul 2
  have hh := hm.neg.div ht (by
    change 2 * Real.sqrt s ^ 3 ≠ 0
    exact mul_ne_zero (by norm_num) (pow_ne_zero _ (Real.sqrt_ne_zero'.mpr hs)))
  change HasDerivAt (fun t => -tfInfiniteCharge (Real.sqrt t) / (2 * (Real.sqrt t)^3)) _ s at hh
  rw [hh.deriv]
  simp only [Pi.pow_apply, Pi.neg_apply, Function.comp_apply, tfFluxSource]
  field_simp [Real.sqrt_ne_zero'.mpr hs]
  ring

lemma tfInfiniteField_classical {x : TFSpace} (hx : x ≠ 0) :
    ContDiffAt ℝ 2 tfInfiniteField x ∧
      Δ tfInfiniteField x = CoulombPDE.reaction tfReactionCoefficient (tfInfiniteField x) := by
  have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx
  let g : ℝ → ℝ := fun s => tfInfiniteRadial (Real.sqrt s)
  have hg : ContDiffAt ℝ 2 g (‖x‖ ^ 2) := by
    have hrp := tfInfiniteRadial_contDiffOn.contDiffAt (Ioi_mem_nhds hn)
    have hrp' : ContDiffAt ℝ 2 tfInfiniteRadial (Real.sqrt (‖x‖ ^ 2)) := by
      rwa [Real.sqrt_sq (norm_nonneg x)]
    exact hrp'.comp (‖x‖ ^ 2) (Real.contDiffAt_sqrt (pow_ne_zero _ hn.ne'))
  have he : tfInfiniteField = (fun y : TFSpace => g (‖y‖ ^ 2)) := by
    funext y
    simp [tfInfiniteField, g, Real.sqrt_sq (norm_nonneg y)]
  have hfull : ContDiffAt ℝ 2 (fun y : TFSpace => g (‖y‖ ^ 2)) x :=
    ContDiffAt.comp (g := g) (f := fun y : TFSpace => ‖y‖ ^ 2) x hg (contDiff_norm_sq ℝ).contDiffAt
  refine ⟨he ▸ hfull, ?_⟩
  rw [he, CoulombPDE.laplacian_norm_sq_comp hg]
  dsimp only [g]
  rw [(tfInfinite_sqrt_hasDerivAt (sq_pos_of_pos hn)).deriv,
    tfInfinite_sqrt_second (sq_pos_of_pos hn), Real.sqrt_sq (norm_nonneg x)]
  have hdim : Module.finrank ℝ TFSpace = 3 := by simp [TFSpace]
  rw [hdim]
  norm_num only [Nat.cast_ofNat]
  field_simp [hn.ne']
  ring

lemma tfInfiniteField_decay : ∀ ε > 0, ∃ R > 0, ∀ x, R ≤ ‖x‖ → |tfInfiniteField x| < ε := by
  intro ε hε
  refine ⟨max 1 (2 * TFUnitData.chargeCap 1 / ε), lt_max_of_lt_left zero_lt_one, ?_⟩
  intro x hx
  have h1 : 1 ≤ ‖x‖ := (le_max_left _ _).trans hx
  have hn : 0 < ‖x‖ := zero_lt_one.trans_le h1
  change |tfInfiniteRadial ‖x‖| < ε
  rw [abs_of_nonneg (tfInfiniteRadial_nonneg hn)]
  apply (tfInfiniteRadial_far_bound zero_lt_one h1).trans_lt
  apply (div_lt_iff₀ hn).mpr
  have hh := (div_le_iff₀ hε).mp ((le_max_right _ _).trans hx)
  have hc := TFUnitData.chargeCap_pos zero_lt_one
  nlinarith

end CoulombAnalysis

end

end OAI
