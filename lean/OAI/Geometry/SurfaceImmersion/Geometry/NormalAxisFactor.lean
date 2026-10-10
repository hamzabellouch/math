import OAI.Geometry.SurfaceImmersion.Geometry.TwoZeroAxisFactor
import OAI.Geometry.SurfaceImmersion.Geometry.PlaneComplexFrame
import OAI.Geometry.SurfaceImmersion.Whitney.NondegenerateCrosscapDefect
import OAI.Geometry.SurfaceImmersion.Correction.CompactSmoothCutoffs

namespace OAI

/-! Normalizing the actual two-zero defect along its connecting axis. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

theorem two_zero_axis_factor {N : Base → Base} {U : Set Base} (hU : IsOpen U)
    (hN : ContDiffOn ℝ ∞ N U) {p q : ℝ} (hpq : p < q)
    (haxis : ∀ t ∈ Icc p q, crosscapAxis t ∈ U)
    (hz : ∀ x ∈ U, N x = 0 ↔ x = crosscapAxis p ∨ x = crosscapAxis q)
    (hDp : Function.Bijective (fderiv ℝ N (crosscapAxis p)))
    (hDq : Function.Bijective (fderiv ℝ N (crosscapAxis q))) :
    ∃ (d : ℝ → Base) (W : Set ℝ), ContDiff ℝ ∞ d ∧ IsOpen W ∧ Icc p q ⊆ W ∧
      (∀ t ∈ Icc p q, d t ≠ 0) ∧
      ∀ t ∈ W, N (crosscapAxis t) = ((t-p)*(t-q)) • d t := by
  let V := crosscapAxis ⁻¹' U
  have hV : IsOpen V := hU.preimage crosscapAxis.continuous
  have hfV : ContDiffOn ℝ ∞ (N ∘ crosscapAxis) V :=
    hN.comp crosscapAxis.contDiff.contDiffOn (fun _ hx => hx)
  obtain ⟨W,hW,hKW,_hWV,g,hg,hge⟩ := CollarVelocity.compact_smooth_extension
    (isCompact_Icc : IsCompact (Icc p q)) hV haxis hfV
  have hgevent (t : ℝ) (ht : t ∈ Icc p q) : g =ᶠ[𝓝 t] N ∘ crosscapAxis :=
    hge.eventuallyEq_of_mem (hW.mem_nhds (hKW ht))
  have hder (t : ℝ) (ht : t ∈ Icc p q) :
      deriv g t = fderiv ℝ N (crosscapAxis t) (![0,1] : Base) := by
    rw [(hgevent t ht).deriv_eq]
    have hd := ((hN.contDiffAt (hU.mem_nhds (haxis t ht))).differentiableAt
      (by simp)).hasFDerivAt.comp_hasDerivAt t crosscapAxis.hasFDerivAt.hasDerivAt
    simpa only [crosscapAxis_apply] using hd.deriv
  have hp : g p = 0 := by
    rw [(hgevent p (left_mem_Icc.mpr hpq.le)).self_of_nhds]
    exact (hz _ (haxis p (left_mem_Icc.mpr hpq.le))).mpr (Or.inl rfl)
  have hq : g q = 0 := by
    rw [(hgevent q (right_mem_Icc.mpr hpq.le)).self_of_nhds]
    exact (hz _ (haxis q (right_mem_Icc.mpr hpq.le))).mpr (Or.inr rfl)
  have hdp : deriv g p ≠ 0 := by
    rw [hder p (left_mem_Icc.mpr hpq.le)]
    intro he
    have h := hDp.1 (he.trans (map_zero _).symm)
    have h1 := congrFun h 1
    norm_num at h1
  have hdq : deriv g q ≠ 0 := by
    rw [hder q (right_mem_Icc.mpr hpq.le)]
    intro he
    have h := hDq.1 (he.trans (map_zero _).symm)
    have h1 := congrFun h 1
    norm_num at h1
  have hzero : ∀ t ∈ Icc p q, g t = 0 → t = p ∨ t = q := by
    intro t ht he
    rw [(hgevent t ht).self_of_nhds] at he
    rcases (hz _ (haxis t ht)).mp he with h | h
    · exact Or.inl (congrFun h 1)
    · exact Or.inr (congrFun h 1)
  obtain ⟨d,hd,he,hn,_hdp,_hdq⟩ := nonzero_two_zero_factor hg hpq.ne hp hq hdp hdq hzero
  refine ⟨d,W,hd,hW,hKW,hn,?_⟩
  intro t ht
  exact (hge ht).symm.trans (he t)

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
