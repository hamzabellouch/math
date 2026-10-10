import OAI.Analysis.LipschitzHilbert.Fourier.SharpBandMeasurableRestricted
import OAI.Analysis.LipschitzHilbert.Estimates.ScalarRestrictedStrong
import OAI.Analysis.LipschitzHilbert.Estimates.L2Indicator

namespace OAI

/-! Uniform strong L2 control of the actual positive-band pairing,
localized in a narrow horizontal strip. -/
noncomputable section
open Set MeasureTheory Function
open scoped ENNReal
namespace LipschitzHilbert.PacketRepresentation

def horizontalStrip (l r : ℝ) : Set (ℝ×ℝ) := {z | z.1∈Icc l r}

theorem horizontalStrip_measurable (l r : ℝ) : MeasurableSet (horizontalStrip l r) :=
  measurable_fst (measurableSet_Icc)

def stripL2Cutoff (l r : ℝ) : Lp ℂ 2 planeMeasure →L[ℂ] Lp ℂ 2 planeMeasure :=
  l2Indicator planeMeasure (horizontalStrip l r) (horizontalStrip_measurable l r)

def localizedSharpBandPairing (epsilon R : ℝ) (he : 0<epsilon) (hR : 0<R)
    (field : Plane → ℝ) (hfield : LipschitzWith 1 field) (p : SchwartzMap ℝ ℂ) (w l r : ℝ) :
    Lp ℂ 2 planeMeasure →L[ℝ] Lp ℂ 2 planeMeasure →L[ℝ] ℂ :=
  (sharpBandL2Pairing epsilon R he hR field hfield p w).bilinearComp
    ((stripL2Cutoff l r).restrictScalars ℝ) ((stripL2Cutoff l r).restrictScalars ℝ)

theorem indicator_unit {X : Type*} (A : Set X) (f : X → ℂ) (hf : ∀ z, ‖f z‖≤1) :
    ∀ z, ‖A.indicator f z‖≤1 := by
  intro z
  by_cases hz : z∈A
  · simpa only [Set.indicator_of_mem hz] using hf z
  · simp only [Set.indicator_of_notMem hz,norm_zero,zero_le_one]

theorem indicator_support_subset {X : Type*} (A F : Set X) (f : X → ℂ)
    (hf : ∀ z, z∉F → f z=0) : support (A.indicator f)⊆F := by
  intro z hz
  by_contra hn
  by_cases ha : z∈A
  · exact hz (by rw [Set.indicator_of_mem ha,hf z hn])
  · exact hz (Set.indicator_of_notMem ha f)

theorem localized_sharp_band_strong (hVariation : LepingleInput) (hLL : LaceyLiInput)
    (hH : HorizontalHilbertInput) (p : SchwartzMap ℝ ℂ) (hp : ∀ s, p s≠0 → 1≤s ∧ s≤2) :
    ∃ C : ℝ, 0<C ∧ ∀ epsilon R w : ℝ, (he : 0<epsilon) → (heR : epsilon≤R) → R≤1/4 → 0<w →
    ∀ (field : Plane → ℝ) (hfield : LipschitzWith 1 field), (∀ z, |field z|≤1/4) →
    ∀ l r : ℝ, 1200*(r-l)≤1 → ∀ f g : Lp ℂ 2 planeMeasure,
      ‖localizedSharpBandPairing epsilon R he (he.trans_le heR) field hfield p w l r f g‖≤C*‖f‖*‖g‖ := by
  obtain ⟨C,hC,hbound⟩ := actual_sharp_band_measurable_restricted_log hVariation hLL hH p hp
  refine ⟨4*C*restrictedStrongConstant,mul_pos (mul_pos (by norm_num) hC) restrictedStrongConstant_pos,?_⟩
  intro epsilon R w he heR hR hw field hfield hfb l r hwidth f g
  apply scalar_restricted_strong_norm planeMeasure _ C hC.le _ f g
  intro F G hF hG hFfin hGfin hFpos hGpos u v hum hvm hu hv hus hvs hu2 hv2
  change ‖sharpBandL2Pairing epsilon R he (he.trans_le heR) field hfield p w
    (stripL2Cutoff l r (hu2.toLp u)) (stripL2Cutoff l r (hv2.toLp v))‖≤_
  unfold stripL2Cutoff
  rw [l2Indicator_toLp,l2Indicator_toLp]
  exact hbound epsilon R w he heR hR hw field hfield hfb
    ((horizontalStrip l r).indicator u) ((horizontalStrip l r).indicator v)
    (hum.indicator (horizontalStrip_measurable l r)) (hvm.indicator (horizontalStrip_measurable l r))
    (indicator_unit _ u hu) (indicator_unit _ v hv) G F hG hF hGfin hFfin hFpos hGpos
    (indicator_support_subset _ F u hus) (indicator_support_subset _ G v hvs) l r hwidth
    (fun z hz => Set.indicator_of_notMem (show z∉horizontalStrip l r from hz) u) (fun z hz => Set.indicator_of_notMem (show z∉horizontalStrip l r from hz) v)
    (hu2.indicator (horizontalStrip_measurable l r)) (hv2.indicator (horizontalStrip_measurable l r))

end LipschitzHilbert.PacketRepresentation

end

end OAI
