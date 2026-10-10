import OAI.Probability.SLE.Geometry.ReflectedRiemannSymmetry
import Mathlib.Analysis.Calculus.Deriv.Slope

namespace OAI

/-! The normalized chart preserves the upper side. Reflection excludes
interior real values, and the positive derivative fixes the component sign. -/
noncomputable section
open Set Complex Filter Function
open scoped Topology ComplexConjugate

namespace SLEExactGauge

lemma real_symmetric_injective_im_ne_zero {D : Set ℂ} {f : ℂ → ℂ}
    (hD : MapsTo conj D D) (hi : InjOn f D)
    (hs : ∀ z ∈ D, f (conj z)=conj (f z)) {z : ℂ} (hz : z ∈ D) (him : 0 < z.im) :
    (f z).im ≠ 0 := by
  intro he
  have hfconj : conj (f z)=f z := by apply Complex.ext <;> simp [he]
  have hzconj := hi (hD hz) hz ((hs z hz).trans hfconj)
  have hh := congrArg Complex.im hzconj
  simp only [conj_im] at hh
  linarith

lemma positive_derivative_upper_witness {D : Set ℂ} (ho : IsOpen D) (h0D : (0:ℂ) ∈ D)
    {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f D) (hf0 : f 0=0)
    {a : ℝ} (ha : 0 < a) (hd : deriv f 0=(a:ℂ)) :
    ∃ z ∈ D, 0 < z.im ∧ 0 < (f z).im := by
  have hfAt : HasDerivAt f (a:ℂ) 0 := by
    rw [← hd]
    exact (hf.differentiableAt (ho.mem_nhds h0D)).hasDerivAt
  have hline : HasDerivAt (fun t : ℝ => (t:ℂ)*I) I 0 := by
    simpa using ((hasDerivAt_id (0:ℝ)).ofReal_comp.mul_const I)
  have hfLine : HasDerivAt f (a:ℂ) ((0:ℂ)*I) := by simpa using hfAt
  have hcomp : HasDerivAt (fun t : ℝ => f ((t:ℂ)*I)) (I*(a:ℂ)) 0 := by
    convert! HasDerivAt.scomp (h := fun t : ℝ => (t:ℂ)*I) (0:ℝ) hfLine hline using 1
  have him : HasDerivAt (fun t : ℝ => (f ((t:ℂ)*I)).im) a 0 := by
    convert! Complex.imCLM.hasFDerivAt.comp_hasDerivAt (0:ℝ) hcomp using 1
    simp
  have hslope : Tendsto (fun t : ℝ => (f ((t:ℂ)*I)).im/t) (𝓝[>] 0) (𝓝 a) := by
    simpa only [zero_add,ofReal_zero,zero_mul,hf0,zero_im,sub_zero,smul_eq_mul,div_eq_inv_mul] using
      him.tendsto_slope_zero_right
  have hpos := hslope.eventually (Ioi_mem_nhds ha)
  have hDnear : ∀ᶠ t : ℝ in 𝓝[>] 0, (t:ℂ)*I ∈ D := by
    have hc : Continuous (fun t : ℝ => (t:ℂ)*I) := by fun_prop
    exact ((hc.tendsto 0).eventually (by simpa using ho.mem_nhds h0D)).filter_mono
      nhdsWithin_le_nhds
  have htp : ∀ᶠ t : ℝ in 𝓝[>] 0, 0 < t := self_mem_nhdsWithin
  obtain ⟨t,ht,hmem,hval⟩ := (htp.and (hDnear.and hpos)).exists
  refine ⟨(t:ℂ)*I,hmem,by simpa using ht,?_⟩
  exact ((div_pos_iff.mp hval).resolve_right (fun h => (not_lt_of_ge ht.le) h.2)).1

theorem normalized_riemann_maps_upper {D : Set ℂ} (ho : IsOpen D) (h0D : (0:ℂ) ∈ D)
    (hD : MapsTo conj D D) (hc : IsPreconnected (D ∩ upperHalfPlane))
    {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f D) (hb : BijOn f D (Metric.ball 0 1))
    (hf0 : f 0=0) {a : ℝ} (ha : 0 < a) (hd : deriv f 0=(a:ℂ)) :
    MapsTo f (D ∩ upperHalfPlane) upperHalfPlane := by
  have hs := normalized_riemann_chart_conj ho h0D hD hf hb hf0 hd
  obtain ⟨w,hw,hwH,hfw⟩ := positive_derivative_upper_witness ho h0D hf hf0 ha hd
  intro z hz
  have hn := real_symmetric_injective_im_ne_zero hD hb.injOn hs hz.1 hz.2
  by_contra hneg
  have hlt : (f z).im < 0 := lt_of_le_of_ne (le_of_not_gt hneg) hn
  have hcont : ContinuousOn (fun z => (f z).im) (D ∩ upperHalfPlane) :=
    Complex.continuous_im.comp_continuousOn (hf.continuousOn.mono inter_subset_left)
  obtain ⟨v,hv,hvim⟩ := hc.intermediate_value hz ⟨hw,hwH⟩ hcont
    (show (0:ℝ) ∈ Icc (f z).im (f w).im from ⟨hlt.le,hfw.le⟩)
  exact real_symmetric_injective_im_ne_zero hD hb.injOn hs hv.1 hv.2 hvim

end SLEExactGauge

end

end OAI
