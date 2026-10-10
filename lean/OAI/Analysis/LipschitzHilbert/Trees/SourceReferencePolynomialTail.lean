import OAI.Analysis.LipschitzHilbert.Trees.SourceReferenceThreshold
import OAI.Analysis.LipschitzHilbert.Trees.SourceMixedReference

namespace OAI

/-! Polynomial exceptional thresholds for the actual mixed reference
packets, conditional only on the published scalar variation input. -/

noncomputable section
open Filter MeasureTheory Set
open scoped Topology ENNReal FourierTransform
namespace LipschitzHilbert.SourceLatticePacket

/-- Constants and the lower bound on L precede all finite packet families,
reference lines, and binary intervals. The two analyzing and synthesis
profiles may differ, as they do in the deterministic residual sequence. -/
theorem mixed_reference_polynomial_tails (hL : LepingleInput) {lo hi : ℝ}
    (hlo : 0 < lo) (hhi : 0 ≤ hi) (a J : ℝ) (ha : 0 ≤ a) (hJ : 0 ≤ J) :
    ∀ᶠ L : ℝ in atTop,
    ∀ (N : ℕ) (κ : Type) (ι : Fin N → Type)
      [Fintype κ] [∀ j, Fintype (ι j)] (P : SourceLatticePacket N κ ι),
      P.constant ≤ L^a →
    ∀ (c : ∀ j, ι j → κ → ℂ) (hc : ∀ j u k, ‖c j u k‖ ≤ 1)
      (alt : ∀ j, ι j → κ → SchwartzMap (ℝ×ℝ) ℂ)
      (hAlt : ∀ j u k, planarProfileConstant (alt j u k) (2*P.order) ≤ P.profileBound)
      (d : Fin N → ℝ) (v : ℝ×ℝ → ℝ) (hv : Measurable v)
      (g : ℝ×ℝ → EuclideanSpace ℂ κ) (hg : Measurable g) (hg1 : ∀ z, ‖g z‖ ≤ 1),
      Monotone d →
      (∀ j u k y xi, |xi| < (lo/P.topLength)*(2:ℝ)^j.val →
        𝓕 ((P.frozenProfile c hc).raw 0 j u k y) xi = 0) →
      (∀ j u k y xi, (hi/P.topLength)*(2:ℝ)^j.val < |xi| →
        𝓕 ((P.frozenProfile c hc).raw 0 j u k y) xi = 0) →
      (∀ j u k y xi, |xi| < (lo/P.topLength)*(2:ℝ)^j.val →
        𝓕 ((P.withProfile alt hAlt).raw 0 j u k y) xi = 0) →
      (∀ j u k y xi, (hi/P.topLength)*(2:ℝ)^j.val < |xi| →
        𝓕 ((P.withProfile alt hAlt).raw 0 j u k y) xi = 0) →
    ∀ (y : ℝ) (grid : FiniteLineGrid), grid.branching = 2 →
      (∀ j (_u : ι j), P.length j ≤ P.topLength*grid.width) →
      let Q := P.mixedReferenceLine c hc alt hAlt d v hv g hg hg1 y
      grid.lineMeasure {x | L^(a+4) ≤ |Q.squareFunction x|} ≤
        ENNReal.ofReal (Real.exp (-J*L))*grid.lineMeasure univ ∧
      grid.lineMeasure {x | L^(a+4) ≤ |Q.variation x|} ≤
        ENNReal.ofReal (Real.exp (-J*L))*grid.lineMeasure univ := by
  obtain ⟨A,M,hA,hM,hm⟩ := mixed_reference_uniform_moments hL hlo hhi
  have hB : 0 ≤ A/Real.pi^4 := by positivity
  filter_upwards [eventually_reference_thresholds M (A/Real.pi^4) a J hM.le hB ha hJ]
    with L hthreshold
  obtain ⟨n,hn,hdecay,hT,hthreshold⟩ := hthreshold
  intro N κ ι _ _ P hP c hc alt hAlt d v hv g hg hg1 hd hAlow hAhigh hSlow hShigh y grid hb hwidth
  let Q := P.mixedReferenceLine c hc alt hAlt d v hv g hg hg1 y
  have hb' : 1 < grid.branching := by omega
  have hmoment := hm N κ ι P c hc alt hAlt d v hv g hg hg1 hd
    hAlow hAhigh hSlow hShigh y grid hb' hwidth
  have hthreshold' := hthreshold grid P.constant hb P.constant_pos.le hP
  have ht := reference_polynomial_tails_of_moments grid.lineMeasure Q.squareFunction Q.variation
    (Q.squareSum_continuous.sqrt.measurable) Q.continuous_variation.measurable
    M (A/Real.pi^4) P.constant (L^(a+4)) grid hB P.constant_pos.le n hn hT
    hthreshold'.1 hthreshold'.2
    (hmoment (2*(n:ℝ)) (by positivity)).1 (hmoment n (by positivity)).2
  have hdecay' : (1/4:ℝ≥0∞)^n ≤ ENNReal.ofReal (Real.exp (-J*L)) := by
    have h := ENNReal.ofReal_le_ofReal hdecay
    rw [ENNReal.ofReal_pow (by norm_num : (0:ℝ) ≤ 1/4)] at h
    norm_num only [ENNReal.ofReal_div_of_pos,ENNReal.ofReal_ofNat] at h
    simpa using h
  exact ⟨ht.1.trans (mul_le_mul' hdecay' le_rfl),
    ht.2.trans (mul_le_mul' hdecay' le_rfl)⟩

end LipschitzHilbert.SourceLatticePacket

end

end OAI
