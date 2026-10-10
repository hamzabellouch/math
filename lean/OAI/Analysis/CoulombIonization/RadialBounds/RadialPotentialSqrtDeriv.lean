import Mathlib
import OAI.Analysis.CoulombIonization.RadialBounds.RadialAxis

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
namespace CoulombAnalysis

lemma radialPotential_sqrt_hasDerivAt {ρ : TFSpace → ℝ} (h1 : Integrable ρ)
    (hp : MemLp ρ (5 / 3)) (hr : IsRadial ρ)
    (hc : ∀ x, x ≠ 0 → ContinuousAt ρ x) {s : ℝ} (hs : 0 < s) :
    HasDerivAt (fun t => radialPotential ρ (Real.sqrt t))
      (-(radialMass ρ (Real.sqrt s)) / (2 * (Real.sqrt s) ^ 3)) s := by
  have hh := (radialPotential_hasDerivAt h1 hp hr hc (Real.sqrt_pos.mpr hs)).comp s
    (Real.hasDerivAt_sqrt hs.ne')
  convert hh using 1 <;> (try rfl)
  field_simp [Real.sqrt_ne_zero'.mpr hs]

lemma radialPotential_sqrt_deriv {ρ : TFSpace → ℝ} (h1 : Integrable ρ)
    (hp : MemLp ρ (5 / 3)) (hr : IsRadial ρ)
    (hc : ∀ x, x ≠ 0 → ContinuousAt ρ x) {s : ℝ} (hs : 0 < s) :
    deriv (fun t => radialPotential ρ (Real.sqrt t)) s =
      -(radialMass ρ (Real.sqrt s)) / (2 * (Real.sqrt s) ^ 3) :=
  (radialPotential_sqrt_hasDerivAt h1 hp hr hc hs).deriv

lemma radialPotential_sqrt_second {ρ : TFSpace → ℝ} (h1 : Integrable ρ)
    (hp : MemLp ρ (5 / 3)) (hr : IsRadial ρ)
    (hc : ∀ x, x ≠ 0 → ContinuousAt ρ x) {s : ℝ} (hs : 0 < s) :
    deriv (deriv (fun t => radialPotential ρ (Real.sqrt t))) s =
      -Real.pi * radialTrace ρ (Real.sqrt s) / (Real.sqrt s) ^ 2 +
        3 * radialMass ρ (Real.sqrt s) / (4 * (Real.sqrt s) ^ 5) := by
  have he : deriv (fun t => radialPotential ρ (Real.sqrt t)) =ᶠ[𝓝 s]
      fun t => -(radialMass ρ (Real.sqrt t)) / (2 * (Real.sqrt t) ^ 3) := by
    filter_upwards [Ioi_mem_nhds hs] with t ht
    exact radialPotential_sqrt_deriv h1 hp hr hc ht
  rw [he.deriv_eq]
  have hm := (radialMass_hasDerivAt h1 hr hc (Real.sqrt_pos.mpr hs)).comp s
    (Real.hasDerivAt_sqrt hs.ne')
  have ht := ((Real.hasDerivAt_sqrt hs.ne').pow 3).const_mul 2
  have hh := hm.neg.div ht (by
    change 2 * Real.sqrt s ^ 3 ≠ 0
    exact mul_ne_zero (by norm_num) (pow_ne_zero _ (Real.sqrt_ne_zero'.mpr hs)))
  change HasDerivAt (fun t => -radialMass ρ (Real.sqrt t) / (2 * (Real.sqrt t) ^ 3)) _ s at hh
  rw [hh.deriv]
  simp only [Pi.pow_apply, Pi.neg_apply, Function.comp_apply]
  field_simp [Real.sqrt_ne_zero'.mpr hs]
  ring

theorem tfPotential_poisson {ρ : TFSpace → ℝ} (h1 : Integrable ρ)
    (hp : MemLp ρ (5 / 3)) (hr : IsRadial ρ)
    (hc : ∀ x, x ≠ 0 → ContinuousAt ρ x) {R : ℝ} (hR : 0 ≤ R)
    (hs : ∀ y, ρ y ≠ 0 → ‖y‖ ≤ R) {x : TFSpace} (hx : x ≠ 0) :
    ContDiffAt ℝ 2 (tfPotential ρ) x ∧ Δ (tfPotential ρ) x = -(4 * Real.pi * ρ x) := by
  have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx
  let g : ℝ → ℝ := fun s => radialPotential ρ (Real.sqrt s)
  have hg : ContDiffAt ℝ 2 g (‖x‖ ^ 2) := by
    have hrp := (radialPotential_contDiffOn h1 hp hr hc).contDiffAt (Ioi_mem_nhds hn)
    have hsq : Real.sqrt (‖x‖ ^ 2) = ‖x‖ := Real.sqrt_sq (norm_nonneg x)
    have hrp' : ContDiffAt ℝ 2 (radialPotential ρ) (Real.sqrt (‖x‖ ^ 2)) := by rwa [hsq]
    exact hrp'.comp (‖x‖ ^ 2) (Real.contDiffAt_sqrt (pow_ne_zero _ hn.ne'))
  have he : tfPotential ρ =ᶠ[𝓝 x] (fun y => g (‖y‖ ^ 2)) := by
    filter_upwards [eventually_ne_nhds hx] with y hy
    dsimp [g]
    rw [Real.sqrt_sq (norm_nonneg y)]
    exact tfPotential_eq_radialPotential h1 hp hr hR hs hy
  have hfull : ContDiffAt ℝ 2 (fun y : TFSpace => g (‖y‖ ^ 2)) x :=
    hg.comp x (contDiff_norm_sq ℝ).contDiffAt
  refine ⟨hfull.congr_of_eventuallyEq he, ?_⟩
  rw [(laplacian_congr_nhds he).eq_of_nhds, CoulombPDE.laplacian_norm_sq_comp hg]
  dsimp only [g]
  rw [radialPotential_sqrt_deriv h1 hp hr hc (sq_pos_of_pos hn),
    radialPotential_sqrt_second h1 hp hr hc (sq_pos_of_pos hn), Real.sqrt_sq (norm_nonneg x),
    ← hr.trace x]
  have hdim : Module.finrank ℝ TFSpace = 3 := by simp [TFSpace]
  rw [hdim]
  norm_num only [Nat.cast_ofNat]
  field_simp [hn.ne']
  ring

end CoulombAnalysis

open MeasureTheory Set Filter Metric Topology InnerProductSpace Laplacian

end

end OAI
