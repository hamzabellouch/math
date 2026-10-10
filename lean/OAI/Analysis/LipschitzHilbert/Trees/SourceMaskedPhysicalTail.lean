import OAI.Analysis.LipschitzHilbert.Trees.SourceMaskedPhysicalMoments
import OAI.Analysis.LipschitzHilbert.Trees.SourceReferenceThreshold

namespace OAI

/-! Polynomial thresholds for the actual masked mixed reference
family. Shortness and the narrow cone supply the mask hypotheses for
every sufficiently large L; no separate mask spectrum is assumed. -/

noncomputable section
open Filter MeasureTheory Set
open scoped Topology ENNReal FourierTransform
namespace LipschitzHilbert.SourceLatticePacket

theorem masked_mixed_reference_polynomial_tails (hVariation : LepingleInput)
    {lo hi : ℝ} (hlo : 0 < lo) (hhi : 0 ≤ hi)
    (q J A cone : ℝ) (hq : 0 ≤ q) (hJ : 0 ≤ J) (hA : 1 < A) (hcone : 0 ≤ cone) :
    ∀ᶠ L : ℝ in atTop,
    ∀ (N : ℕ) (κ : Type) (ι : Fin N → Type)
      [Fintype κ] [∀ j, Fintype (ι j)] (P : SourceLatticePacket N κ ι),
      P.constant ≤ L^q →
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
    ∀ (T : ∀ j, ι j → SlopeBox) (t : ℝ),
      (∀ j u, P.length j ≤ (T j u).length) →
      (∀ j u, |t-(T j u).slope| ≤ cone*(T j u).width/P.length j) →
    ∃ rate : ∀ j u, 2*(⌈L⌉₊:ℝ)*
      (|(T j u).maskLineA L A|+|(T j u).maskLineC L A t|) ≤ 1/P.length j,
    ∀ (y : ℝ) (grid : FiniteLineGrid), grid.branching = 2 →
      (∀ j (_u : ι j), P.length j ≤ P.topLength*grid.width) →
      let Q := P.maskedMixedReferenceLine c hc alt hAlt d v hv g hg hg1 T L A t y rate
      grid.lineMeasure {x | L^(q+5) ≤ |Q.squareFunction x|} ≤
        ENNReal.ofReal (Real.exp (-J*L))*grid.lineMeasure univ ∧
      grid.lineMeasure {x | L^(q+5) ≤ |Q.variation x|} ≤
        ENNReal.ofReal (Real.exp (-J*L))*grid.lineMeasure univ := by
  obtain ⟨B,M,hB,hM,hm⟩ := masked_mixed_reference_uniform_moments hVariation hlo hhi
  filter_upwards [eventually_reference_thresholds M B (q+1) J hM.le hB.le (by linarith) hJ,
    SlopeBox.eventually_mask_scalar_small hA hcone hlo,
    eventually_ge_atTop (2:ℝ)] with L hthreshold hsmall hL2
  have hL : 0 < L := lt_of_lt_of_le (by norm_num) hL2
  obtain ⟨n,hn,hdecay,hT,hthreshold⟩ := hthreshold
  rw [show (q+1)+4 = q+5 by ring] at hT hthreshold
  intro N κ ι _ _ P hP c hc alt hAlt d v hv g hg hg1 hd
    hAlow hAhigh hSlow hShigh T t hshort hcone'
  let rate := P.physicalReferenceMaskRate T L A t cone lo hL hshort hcone' hsmall
  refine ⟨rate,?_⟩
  intro y grid hb hwidth
  let Q := P.maskedMixedReferenceLine c hc alt hAlt d v hv g hg hg1 T L A t y rate
  have hC : 2*P.constant ≤ L^(q+1) := by
    calc
      _ ≤ L*L^q := mul_le_mul hL2 hP P.constant_pos.le hL.le
      _ = _ := by rw [Real.rpow_add hL,Real.rpow_one]; ring
  have hC0 : 0 ≤ 2*P.constant := mul_nonneg (by norm_num) P.constant_pos.le
  have hb' : 1 < grid.branching := by omega
  have hmoment := hm N κ ι P c hc alt hAlt d v hv g hg hg1 hd
    hAlow hAhigh hSlow hShigh T L A t cone hL hshort hcone' hsmall y grid hb' hwidth
  have ht := hthreshold grid (2*P.constant) hb hC0 hC
  have htail := reference_polynomial_tails_of_moments grid.lineMeasure Q.squareFunction Q.variation
    (Q.squareSum_continuous.sqrt.measurable) Q.continuous_variation.measurable
    M B (2*P.constant) (L^(q+5)) grid hB.le hC0 n hn hT ht.1 ht.2
    (hmoment (2*(n:ℝ)) (by positivity)).1 (hmoment n (by positivity)).2
  have hdecay' : (1/4:ℝ≥0∞)^n ≤ ENNReal.ofReal (Real.exp (-J*L)) := by
    have h := ENNReal.ofReal_le_ofReal hdecay
    rw [ENNReal.ofReal_pow (by norm_num : (0:ℝ) ≤ 1/4)] at h
    norm_num only [ENNReal.ofReal_div_of_pos,ENNReal.ofReal_ofNat] at h
    simpa using h
  exact ⟨htail.1.trans (mul_le_mul' hdecay' le_rfl),
    htail.2.trans (mul_le_mul' hdecay' le_rfl)⟩

end LipschitzHilbert.SourceLatticePacket

end

end OAI
