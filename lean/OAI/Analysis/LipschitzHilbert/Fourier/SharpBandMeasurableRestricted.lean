import OAI.Analysis.LipschitzHilbert.Fourier.SharpBandRestrictedLog
import OAI.Analysis.LipschitzHilbert.Fourier.BandL2Pairing
import OAI.Analysis.LipschitzHilbert.Estimates.RestrictedLogDensity

namespace OAI

/-! The actual sharp band logarithmic estimate for bounded measurable
L2 tests. The slight strip margin is used only for smooth approximation. -/
noncomputable section
open Set MeasureTheory Function
open scoped ENNReal
namespace LipschitzHilbert.PacketRepresentation

def sharpBandL2Pairing (epsilon R : ℝ) (he : 0<epsilon) (hR : 0<R)
    (field : Plane → ℝ) (hfield : LipschitzWith 1 field) (p : SchwartzMap ℝ ℂ) (w : ℝ) :
    Lp ℂ 2 planeMeasure →L[ℝ] Lp ℂ 2 planeMeasure →L[ℝ] ℂ :=
  bandL2Pairing (sharpTimeKernel epsilon R) (sharpTimeKernel_measurable epsilon R)
    (sharpTimeKernel_integrable epsilon R he hR) (fun z => field (planeCoordinates z))
    (by simpa only [mul_one] using product_slope_lipschitz field hfield) p w

theorem support_into_open_strip (f : (ℝ×ℝ) → ℂ) (l r : ℝ)
    (hf : ∀ z, z.1∉Icc l r → f z=0) :
    support f⊆{z : ℝ×ℝ | z.1∈Ioo (l-1/2400) (r+1/2400)} := by
  intro z hz
  have hi : z.1∈Icc l r := by
    by_contra hn
    exact hz (hf z hn)
  constructor <;> linarith only [hi.1,hi.2]

theorem schwartz_open_strip_zero (f : SchwartzMap (ℝ×ℝ) ℂ) (l r : ℝ)
    (hf : support f⊆{z : ℝ×ℝ | z.1∈Ioo l r}) :
    ∀ z, z.1∉Icc l r → f z=0 := by
  intro z hz
  apply notMem_support.mp
  intro hs
  exact hz (Ioo_subset_Icc_self (hf hs))

theorem actual_sharp_band_measurable_restricted_log
    (hVariation : LepingleInput) (hLL : LaceyLiInput) (hH : HorizontalHilbertInput)
    (p : SchwartzMap ℝ ℂ) (hp : ∀ s, p s≠0 → 1≤s ∧ s≤2) :
    ∃ C : ℝ, 0<C ∧ ∀ epsilon R w : ℝ, (he : 0<epsilon) → (heR : epsilon≤R) → R≤1/4 → 0<w →
    ∀ (field : Plane → ℝ) (hfield : LipschitzWith 1 field), (∀ z, |field z|≤1/4) →
    ∀ (f g : (ℝ×ℝ) → ℂ), Measurable f → Measurable g →
      (∀ z, ‖f z‖≤1) → (∀ z, ‖g z‖≤1) →
    ∀ E F : Set (ℝ×ℝ), MeasurableSet E → MeasurableSet F → planeMeasure E≠∞ → planeMeasure F≠∞ →
      0<planeMeasure.real F → 0<planeMeasure.real E → support f⊆F → support g⊆E →
    ∀ l r : ℝ, 1200*(r-l)≤1 → (∀ z, z.1∉Icc l r → f z=0) → (∀ z, z.1∉Icc l r → g z=0) →
    ∀ (hf2 : MemLp f 2 planeMeasure) (hg2 : MemLp g 2 planeMeasure),
      ‖sharpBandL2Pairing epsilon R he (he.trans_le heR) field hfield p w (hf2.toLp f) (hg2.toLp g)‖≤
        restrictedLogFactor C (planeMeasure.real F) (planeMeasure.real E) := by
  obtain ⟨C,hC,hbound⟩ := actual_sharp_band_restricted_log hVariation hLL hH p hp
  refine ⟨C,hC,?_⟩
  intro epsilon R w he heR hR hw field hfield hfb f g hfm hgm hf hg E F hE hF hEfin hFfin
    hFpos hEpos hfs hgs l r hwidth hfstrip hgstrip hf2 hg2
  let V := {z : ℝ×ℝ | z.1∈Ioo (l-1/2400) (r+1/2400)}
  have hV : IsOpen V := isOpen_Ioo.preimage continuous_fst
  have hwide : 600*((r+1/2400)-(l-1/2400))≤1 := by linarith only [hwidth]
  apply restricted_log_density _ C V hV _ f g hfm hgm hf hg
    (support_into_open_strip f l r hfstrip) (support_into_open_strip g l r hgstrip)
    F E hF hE hFfin hEfin hFpos hEpos hfs hgs hf2 hg2
  intro fn gn hfnb hgnb hfnV hgnV Fn Gn hFn hGn hFnfin hGnfin hFnpos hGnpos hfns hgns
  have hfnstrip := schwartz_open_strip_zero fn (l-1/2400) (r+1/2400) hfnV
  have hgnstrip := schwartz_open_strip_zero gn (l-1/2400) (r+1/2400) hgnV
  have hb := hbound epsilon R w he heR hR hw field hfield hfb fn gn hfnb hgnb Gn Fn
    hGn hFn hGnfin hFnfin hFnpos hGnpos
    (fun z hz => notMem_support.mp (fun hs => hz (hgns hs)))
    (fun z hz => notMem_support.mp (fun hs => hz (hfns hs)))
    (l-1/2400) (r+1/2400) hwide hfnstrip hgnstrip
  change ‖bandL2Pairing _ _ _ _ _ p w _ _‖≤_
  rw [bandL2Pairing_kernel _ _ _ _ _ p w hw fn gn (l-1/2400) (r+1/2400)
    (by linarith only [hwide]) hfnstrip hgnstrip]
  exact hb

end LipschitzHilbert.PacketRepresentation

end

end OAI
