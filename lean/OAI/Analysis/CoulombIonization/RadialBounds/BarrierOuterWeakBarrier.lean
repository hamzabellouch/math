import Mathlib
import OAI.Analysis.CoulombIonization.ThomasFermi.WeakSommerfeldBoundsBarrier
import OAI.Analysis.CoulombIonization.RadialBounds.BarrierTowerBarrier
import OAI.Analysis.CoulombIonization.RadialBounds.BarrierRetainedComparisonBarrier

namespace OAI

noncomputable section

namespace CoulombBarrier

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
section Work_BarrierOuterWeak_barrier_scope

open Set Filter MeasureTheory Laplacian Metric InnerProductSpace
open scoped Topology ContDiff

open CoulombAnalysis

def clippedOuterBarrier (B r : ℝ) (x : TFSpace) : ℝ :=
  B/(max r ‖x‖)^4*(1-r/(8*max r ‖x‖))

def outerOffset (Z B r : ℝ) (x : TFSpace) : ℝ :=
  clippedOuterBarrier B r x-clippedNuclearField Z r x

lemma clippedOuterBarrier_continuous (B : ℝ) {r : ℝ} (hr : 0 < r) :
    Continuous (clippedOuterBarrier B r) := by
  have hm : Continuous (fun x : TFSpace => max r ‖x‖) := continuous_const.max continuous_norm
  have hn (x : TFSpace) : max r ‖x‖ ≠ 0 := (hr.trans_le (le_max_left _ _)).ne'
  exact (continuous_const.div (hm.pow 4) (fun x => pow_ne_zero _ (hn x))).mul
    (continuous_const.sub (continuous_const.div (continuous_const.mul hm)
      (fun x => mul_ne_zero (by norm_num) (hn x))))

lemma outerOffset_continuous (Z B : ℝ) {r : ℝ} (hr : 0 < r) :
    Continuous (outerOffset Z B r) :=
  (clippedOuterBarrier_continuous B hr).sub (clippedNuclearField_continuous Z hr)

lemma clippedOuterBarrier_eq {B r : ℝ} {x : TFSpace} (hx : r ≤ ‖x‖) :
    clippedOuterBarrier B r x = outerBarrier B r x := by
  simp only [clippedOuterBarrier,outerBarrier,max_eq_right hx]

lemma nuclear_outerOffset_eq {Z B r : ℝ} {x : TFSpace} (hx : r ≤ ‖x‖) :
    nuclearField Z x+outerOffset Z B r x = outerBarrier B r x := by
  simp only [outerOffset,clippedNuclearField,max_eq_right hx,
    clippedOuterBarrier_eq hx,nuclearField]
  ring

lemma WeakNuclearLowerOn.mono_set {U V : Set TFSpace} {Z : ℝ} {u h : TFSpace → ℝ}
    (hw : WeakNuclearLowerOn U Z u h) (hVU : V ⊆ U) :
    WeakNuclearLowerOn V Z u h := fun φ hφ hc hs hn => hw φ hφ hc (hs.trans hVU) hn

lemma weakNuclearLower_iff_off_origin {U : Set TFSpace} (hU : (0 : TFSpace) ∉ U)
    (Z : ℝ) (u h : TFSpace → ℝ) :
    WeakNuclearLowerOn U Z u h ↔ WeakLaplacianLowerOn U u h := by
  have hzero {φ : TFSpace → ℝ} (hs : tsupport φ ⊆ U) : φ 0 = 0 :=
    image_eq_zero_of_notMem_tsupport (fun hx => hU (hs hx))
  constructor
  · intro hw φ hφ hc hs hn
    have hh := hw φ hφ hc hs hn
    simpa only [hzero hs,mul_zero,zero_add] using hh
  · intro hw φ hφ hc hs hn
    simpa only [hzero hs,mul_zero,zero_add] using hw φ hφ hc hs hn

lemma WeakNuclearLowerOn.congr_field {U : Set TFSpace} {Z : ℝ} {u v h : TFSpace → ℝ}
    (hw : WeakNuclearLowerOn U Z u h) (he : ∀ x ∈ U, u x = v x) :
    WeakNuclearLowerOn U Z v h := by
  intro φ hφ hc hs hn
  calc
    _ ≤ ∫ x, u x*Δ φ x := hw φ hφ hc hs hn
    _ = _ := integral_congr_ae (ae_of_all _ fun x => by
      dsimp only
      by_cases hx : Δ φ x = 0
      · simp only [hx,mul_zero]
      · rw [he x (hs (tfLaplacian_support hφ hx))])

lemma WeakNuclearLowerOn.congr_source {U : Set TFSpace} {Z : ℝ} {u h h' : TFSpace → ℝ}
    (hw : WeakNuclearLowerOn U Z u h) (he : ∀ x ∈ U, h x = h' x) :
    WeakNuclearLowerOn U Z u h' := by
  intro φ hφ hc hs hn
  have hh : (∫ x, h' x*φ x) = ∫ x, h x*φ x := by
    apply integral_congr_ae
    filter_upwards [] with x
    by_cases hx : φ x = 0
    · simp only [hx,mul_zero]
    · rw [he x (hs (subset_tsupport φ hx))]
  rw [hh]
  exact hw φ hφ hc hs hn

theorem outerOffset_weak_nuclear {B r k : ℝ} (hB : 0 < B) (hr : 0 < r)
    (hk : 0 ≤ k) (hsmall : 4*Real.pi*k*Real.sqrt B ≤ 19/2) (Z : ℝ) :
    WeakNuclearLowerOn {x : TFSpace | r < ‖x‖} Z
      (fun x => nuclearField Z x+outerOffset Z B r x)
      (fun x => reaction k (nuclearField Z x+outerOffset Z B r x)) := by
  have he {x : TFSpace} (hx : r < ‖x‖) :
      clippedOuterBarrier B r =ᶠ[𝓝 x] outerBarrier B r := by
    filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds hx] with y hy
    exact clippedOuterBarrier_eq hy.le
  have hc := clippedOuterBarrier_continuous B hr
  have hw := classical_weak_lower (isOpen_lt continuous_const continuous_norm) hc
    ((reaction_continuous k).comp hc).locallyIntegrable
    (fun x hx => (outerBarrier_contDiffAt B r (norm_ne_zero_iff.mp (hr.trans hx).ne')).congr_of_eventuallyEq (he hx))
    (fun x hx => by
      dsimp only [Function.comp_def]
      rw [clippedOuterBarrier_eq hx.le,(laplacian_congr_nhds (he hx)).eq_of_nhds]
      exact outerBarrier_subsolution hB hr hk hsmall hx.le)
  have hn := (weakNuclearLower_iff_off_origin (Z := Z)
    (u := clippedOuterBarrier B r) (h := fun x => reaction k (clippedOuterBarrier B r x))
    (by change ¬ r < ‖(0:TFSpace)‖; simpa only [norm_zero,not_lt] using hr.le)).mpr hw
  apply (hn.congr_field (fun x hx => (clippedOuterBarrier_eq hx.le).trans (nuclear_outerOffset_eq hx.le).symm)).congr_source
  intro x hx
  rw [clippedOuterBarrier_eq hx.le,nuclear_outerOffset_eq hx.le]

end Work_BarrierOuterWeak_barrier_scope

open Set Filter MeasureTheory Laplacian Metric
open scoped Topology ContDiff

open CoulombAnalysis

lemma nuclear_source_locallyIntegrable (Z k : ℝ) {r : ℝ} (hr : 0 < r)
    {g χ u : TFSpace → ℝ} (hg : LocallyIntegrable g) (hχ : Measurable χ)
    (hbχ : ∀ x, ‖χ x‖ ≤ 1) (hzero : ∀ x, ‖x‖ < r → χ x = 0)
    (hu : Continuous u) :
    LocallyIntegrable (fun x => g x+χ x*reaction k (nuclearField Z x+u x)) := by
  simp_rw [weighted_clipped_reaction Z r hzero]
  exact semilinear_source_locallyIntegrable hg hχ hbχ (reaction_continuous k)
    ((clippedNuclearField_continuous Z hr).add hu)

lemma nuclear_weak_maximum {U : Set TFSpace} (hU : IsOpen U) (Z k : ℝ)
    {r : ℝ} (hr : 0 < r) {u v g χ : TFSpace → ℝ}
    (hu : Continuous u) (hv : Continuous v) (hg : LocallyIntegrable g)
    (hχ : Measurable χ) (hbχ : ∀ x, ‖χ x‖ ≤ 1)
    (hzero : ∀ x, ‖x‖ < r → χ x = 0)
    (hwu : WeakNuclearLowerOn U Z (fun x => nuclearField Z x+u x)
      (fun x => g x+χ x*reaction k (nuclearField Z x+u x)))
    (hwv : WeakNuclearLowerOn U Z (fun x => nuclearField Z x+v x)
      (fun x => g x+χ x*reaction k (nuclearField Z x+v x))) :
    WeakNuclearLowerOn U Z (fun x => nuclearField Z x+max (u x) (v x))
      (fun x => g x+χ x*reaction k (nuclearField Z x+max (u x) (v x))) := by
  rw [weakNuclearLower_add_iff Z (hu.max hv).locallyIntegrable]
  simp_rw [weighted_clipped_reaction Z r hzero]
  apply weak_maximum_spatial hU hu hv hg hχ hbχ
    (F := fun x t => reaction k (clippedNuclearField Z r x+t))
    ((reaction_continuous k).comp (((clippedNuclearField_continuous Z hr).comp continuous_fst).add continuous_snd))
  · simpa only [weighted_clipped_reaction Z r hzero] using
      (weakNuclearLower_add_iff Z hu.locallyIntegrable).mp hwu
  · simpa only [weighted_clipped_reaction Z r hzero] using
      (weakNuclearLower_add_iff Z hv.locallyIntegrable).mp hwv

lemma WeakNuclearLowerOn.source_mono {U : Set TFSpace} {Z : ℝ} {u h h' : TFSpace → ℝ}
    (hw : WeakNuclearLowerOn U Z u h) (hh : LocallyIntegrable h) (hh' : LocallyIntegrable h')
    (hle : ∀ x ∈ U, h' x ≤ h x) : WeakNuclearLowerOn U Z u h' := by
  intro φ hφ hc hs hn
  apply le_trans _ (hw φ hφ hc hs hn)
  apply add_le_add_right
  apply integral_mono (locallyIntegrable_mul_test hh' hφ.continuous hc)
    (locallyIntegrable_mul_test hh hφ.continuous hc)
  intro x
  dsimp only
  by_cases hx : φ x = 0
  · simp only [hx,mul_zero,le_refl]
  · exact mul_le_mul_of_nonneg_right (hle x (hs (subset_tsupport φ hx))) (hn x)

def cutMaximum (r R : ℝ) (u v : TFSpace → ℝ) (x : TFSpace) : ℝ :=
  if ‖x‖ < r then u x else if ‖x‖ < R then max (u x) (v x) else v x

end CoulombBarrier

end

end OAI
