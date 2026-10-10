import OAI.Probability.GammaPassage.TiltEnvelope
import OAI.Probability.GammaPassage.TiltRegionCount
import OAI.Probability.GammaPassage.CrossingEvents
import OAI.Probability.FirstPassage.TiltPath

namespace OAI

namespace GammaFPP.CrossingBridge
open PlanarFPP GammaFPP.Tilt Set Finset MeasureTheory ProbabilityTheory Filter
open scoped Topology

theorem crossingEvent_tilt_implication (b m a K lam s : ℝ) (n : ℤ)
    (hK : 0 ≤ K) (hlam : 0 ≤ lam) (hs : 0 < s) (hn : 0 < n)
    (hsmall : lam*s < n) (hgain : K+16*|a|+1 < lam*m)
    (w : Edge → ℝ) (hw : w ∈ crossingEvent b m K s n 0) :
    scaleFiniteEdges (internalEdges (rareFastVertices b 1 8 s n 0)) (1-lam*s/n) w ∈
      rareFastEvent b m a 1 8 1 s n 0 := by
  rw [scaleFiniteEdges_event_iff _ _ _ (rareFastEvent_depends b m a 1 8 1 s n 0)]
  obtain ⟨p,ds,⟨hp,hq⟩,hin,hcost⟩ := hw
  have hx : ((displacement ds).1 : ℝ)=(n : ℝ) := by
    have he : (displacement ds).1=n := by simpa [Prod.fst_add,hp] using hq
    exact_mod_cast he
  have hstart : p ∈ rareFastRegion b 1 8 s n 0 := by
    have hh := hin 0 (by omega)
    simpa using hh
  have hend : p+displacement ds ∈ rareFastRegion b 1 8 s n 0 := by
    exact (mem_rareFastVertices ..).mp (pathIn_endpoint _ _ _ hin)
  have hr : |transverse b (displacement ds)| ≤ 16*s := by
    have ht := abs_sub_le (transverse b (p+displacement ds)) 0 (transverse b p)
    simp only [sub_zero, zero_sub, abs_neg] at ht
    simp only [transverse_add,add_sub_cancel_left] at ht
    have h1 := hstart.2.2
    have h2 := hend.2.2
    simp only [sub_zero,transverse_add] at h1 h2
    linarith
  have hd := tilt_crossing_defect w b m a K lam s n hK hlam hs
    (by exact_mod_cast hn) hsmall hgain p ds hx hr hcost
  apply (mem_rareFastEvent ..).mpr
  refine ⟨p,ds,hp,hq,?_,?_⟩
  · intro i hi
    exact (mem_rareFastVertices ..).mp (hin i hi)
  · simpa using hd

theorem source_tilt_exponent_bound (N : ℕ) (lam s n : ℝ)
    (_hs : 0 ≤ s) (hn : 0 < n) (hN : (N : ℝ) ≤ 144*n*s) (hn3 : s^3 ≤ n) :
    2*N*(lam*s/n)^2 ≤ 288*lam^2 := by
  calc
    _ ≤ (2*(144*n*s))*(lam*s/n)^2 := by gcongr
    _ = (288*lam^2)*(s^3/n) := by field_simp; ring
    _ ≤ (288*lam^2)*1 := mul_le_mul_of_nonneg_left ((div_le_one hn).mpr hn3) (by positivity)
    _ = _ := mul_one _

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {τ : Edge → Ω → ℝ}

/-- Squared change-of-measure estimate, with a constant independent of `s`
and `n` whenever `n ≥ s^3`. -/
theorem gamma_crossing_tilt_bound {shape rate : ℝ}
    (h : GammaEnvironment shape rate P τ) (hshape : 0 < shape) (hrate : 0 < rate)
    (b m a K lam s : ℝ) (n : ℤ) (hK : 0 ≤ K) (hlam : 0 ≤ lam)
    (hs : 1 ≤ s) (hn : 1 ≤ n) (hn3 : s^3 ≤ n)
    (hsmall : lam*s/n ≤ 1/2) (hgain : K+16*|a|+1 < lam*m) :
    P.real {ω | (fun e => τ e ω) ∈ crossingEvent b m K s n 0} ^ 2 ≤
      Real.exp (288*shape*lam^2) *
        P.real {ω | (fun e => τ e ω) ∈ rareFastEvent b m a 1 8 1 s n 0} := by
  let _ := h.probability
  let S := internalEdges (rareFastVertices b 1 8 s n 0)
  let F := rareFastEvent b m a 1 8 1 s n 0
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hδ : 0 ≤ lam*s/n := by positivity
  have hlt : lam*s < n := by
    have hh := (div_le_iff₀ hn0).mp hsmall
    linarith
  have himp : {ω | (fun e => τ e ω) ∈ crossingEvent b m K s n 0} ⊆
      {ω | scaleFiniteEdges S (1-lam*s/n) (fun e => τ e ω) ∈ F} := by
    intro ω hω
    exact crossingEvent_tilt_implication b m a K lam s n hK hlam (by linarith) (by omega) hlt hgain _ hω
  have hprob := measureReal_mono (μ := P) himp
  have hcomp := finite_edge_tilt_probability_sq_exp_bound h hshape hrate S (lam*s/n) hδ hsmall F
    (measurableSet_rareFastEvent ..) (rareFastEvent_depends b m a 1 8 1 s n 0)
  have hexp : Real.exp (2*shape*S.card*(lam*s/n)^2) ≤ Real.exp (288*shape*lam^2) := by
    apply Real.exp_le_exp.mpr
    have hh := mul_le_mul_of_nonneg_left
      (source_tilt_exponent_bound S.card lam s n (by linarith) hn0
        (rareFast_tilt_edges_card b s n hs hn) hn3) hshape.le
    nlinarith
  exact (pow_le_pow_left₀ measureReal_nonneg hprob 2).trans
    (hcomp.trans (mul_le_mul_of_nonneg_right hexp measureReal_nonneg))

end GammaFPP.CrossingBridge

end OAI
