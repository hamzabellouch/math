import OAI.Probability.SLE.Geometry.HarmonicTailMaximum

namespace OAI

/-! A single deterministic subsequence makes the harmonic oscillation
uniform over every later compact localization interval. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal

namespace SLEExactGauge
open Target
namespace SmoothDomainExhaustion
variable {U : Set (ℝ×ℝ)} (e : SmoothDomainExhaustion U 0)

theorem harmonic_uniform_tails
    (W : WienerLaw) (hW : IsWiener W) (T : ℝ≥0) (hU : IsOpen U)
    (u : ℝ×ℝ → ℝ) (hu : ContDiffOn ℝ (⊤ : ℕ∞) u U)
    (hhar : ∀ z∈U, planarGenerator u z=0)
    (C : ℝ≥0) (huC : ∀ z∈U, |u z|≤C)
    (Y : Driver×Driver → ℝ)
    (hY : ∀ᵐ b ∂W.prod W,
      Tendsto (fun n => u (planarWiener (e.stop T n b) b)) atTop (𝓝 (Y b)))
    (hE : Tendsto (fun n => ∫ b, |u (planarWiener (e.stop T n b) b)-Y b| ∂W.prod W)
      atTop (𝓝 0)) :
    ∃ N : ℕ → ℕ, (∀ j, j ≤ N j) ∧
      ∀ᵐ b ∂W.prod W, ∀ᶠ j in atTop,
        b∉e.harmonicTailEvent T u (N j) ((1/2:ℝ≥0)^j) := by
  let ε (j : ℕ) : ℝ≥0 := (1/2)^j
  have hε (j) : 0 < ε j := pow_pos (by norm_num) j
  have hchoose (j : ℕ) : ∃ k : ℕ, j ≤ k ∧
      (∫ b, |u (planarWiener (e.stop T k b) b)-Y b| ∂W.prod W) ≤ (ε j:ℝ)^2 := by
    have hp : (0:ℝ) < (ε j:ℝ)^2 := sq_pos_of_pos (hε j)
    obtain ⟨M,hM⟩ := eventually_atTop.mp (hE.eventually (eventually_lt_nhds hp))
    exact ⟨max j M,le_max_left _ _,(hM _ (le_max_right _ _)).le⟩
  choose N hNj hNE using hchoose
  refine ⟨N,hNj,?_⟩
  have hprob (j) : (W.prod W) (e.harmonicTailEvent T u (N j) (ε j)) ≤ (ε j:ℝ≥0∞) := by
    have hh := e.harmonic_tail_maximal W hW T hU u hu hhar C huC Y hY (N j) (ε j)
    have herr : (∫ b, |Y b-u (planarWiener (e.stop T (N j) b) b)| ∂W.prod W) ≤ (ε j:ℝ)^2 := by
      simpa only [abs_sub_comm] using hNE j
    have hmul : (ε j:ℝ≥0∞)*(W.prod W) (e.harmonicTailEvent T u (N j) (ε j)) ≤
        (ε j:ℝ≥0∞)*(ε j:ℝ≥0∞) := by
      calc
        _ ≤ ENNReal.ofReal ((ε j:ℝ)^2) := hh.trans (ENNReal.ofReal_le_ofReal herr)
        _ = _ := by rw [pow_two,ENNReal.ofReal_mul (ε j).coe_nonneg]; simp
    exact (ENNReal.mul_le_mul_iff_right (ENNReal.coe_ne_zero.mpr (hε j).ne') ENNReal.coe_ne_top).mp hmul
  have hsum : (∑' j, (ε j:ℝ≥0∞)) ≠ ∞ := by
    simpa [ε,ENNReal.ofReal_pow] using summable_geometric_two.tsum_ofReal_ne_top
  exact ae_eventually_notMem (ne_top_of_le_ne_top hsum (ENNReal.tsum_le_tsum hprob))

theorem boundary_limit_of_uniform_tail
    (T : ℝ≥0) (u : ℝ×ℝ → ℝ) (b : Driver×Driver) (Y : ℝ)
    (N : ℕ → ℕ) (hN : ∀ j, j ≤ N j)
    (hconv : Tendsto (fun n => u (planarWiener (e.stop T n b) b)) atTop (𝓝 Y))
    (hgood : ∀ᶠ j in atTop, b∉e.harmonicTailEvent T u (N j) ((1/2:ℝ≥0)^j))
    (τ : ℝ≥0) (hτT : τ ≤ T) (hpath : ∀ t<τ, planarWiener t b∈U)
    (hexit : planarWiener τ b∉U) :
    Tendsto (fun t => u (planarWiener t b)) (𝓝[<] τ) (𝓝 Y) := by
  have hNt : Tendsto N atTop atTop := tendsto_atTop.2 fun a =>
    eventually_atTop.2 ⟨a,fun j hj => hj.trans (hN j)⟩
  have hsub := hconv.comp hNt
  have hstop := e.stop_tendsto_finite_exit T τ hτT b hpath hexit
  have hlt (n) : e.stop T n b < τ := by
    have hle : e.stop T n b ≤ τ := ge_of_tendsto hstop (by
      filter_upwards [eventually_ge_atTop n] with m hm
      exact e.stop_monotone T b hm)
    exact lt_of_le_of_ne hle (fun heq => hexit (heq ▸ e.stop_mem_domain T n b _ le_rfl))
  have hε : Tendsto (fun j : ℕ => ((1/2:ℝ≥0)^j:ℝ)) atTop (𝓝 0) := by
    simpa only [NNReal.coe_pow,NNReal.coe_div,NNReal.coe_one,NNReal.coe_ofNat] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (1/2:ℝ)<1))
  apply Metric.tendsto_nhds.2
  intro δ hδ
  obtain ⟨j,hjg,hje,hjx⟩ := (hgood.and ((hε.eventually (eventually_lt_nhds (half_pos hδ))).and
    (hsub.eventually (Metric.ball_mem_nhds Y (half_pos hδ))))).exists
  have hjx' : |u (planarWiener (e.stop T (N j) b) b)-Y| < δ/2 := by
    simpa only [Metric.mem_ball,Real.dist_eq,Function.comp_apply] using hjx
  filter_upwards [self_mem_nhdsWithin,
    nhdsWithin_le_nhds (Ioi_mem_nhds (hlt (N j)))] with t htτ htN
  have ht : t < τ := htτ
  obtain ⟨k,hk,hkt⟩ := ((eventually_ge_atTop (N j)).and
    (hstop.eventually (eventually_gt_nhds ht))).exists
  obtain ⟨m,rfl⟩ := Nat.exists_eq_add_of_le hk
  have hsmall : |u (planarWiener t b)-u (planarWiener (e.stop T (N j) b) b)| ≤ ((1/2:ℝ≥0)^j:ℝ) := by
    apply not_lt.mp
    intro hbad
    exact hjg ⟨m,t,⟨htN.le,hkt.le⟩,hbad⟩
  rw [Real.dist_eq]
  exact (abs_sub_le _ _ _).trans_lt (by linarith)

end SmoothDomainExhaustion
end SLEExactGauge

end

end OAI
