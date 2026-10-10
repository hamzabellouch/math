import OAI.Probability.SLE.Mass.CanonicalMassContinuity

namespace OAI

/-! Rational first-visit identities extend simultaneously to all finite
times by local total-variation continuity. -/

noncomputable section
open Set Filter MeasureTheory Classical
open scoped NNReal ENNReal Topology CompactlySupported

namespace SLEExactGauge.Multipoint

local instance : LocallyCompactSpace upperHalfPlane := isOpen_upperHalfPlane.locallyCompactSpace

theorem trace_restriction_of_rational_times
    (γ : ℝ≥0 → ℂ) (hγ : Continuous γ)
    (μ : ℚ → Measure upperHalfPlane) (ν : Measure upperHalfPlane)
    [ν.Regular] (N : ℝ≥0 → Measure upperHalfPlane)
    (hp : ContinuousMassPath γ μ ν N)
    (hpast : ∀ t, N t {z : upperHalfPlane | (z:ℂ) ∉ γ '' Icc 0 t} = 0)
    (hq : ∀ q : ℚ, 0 ≤ q → N (q:ℝ).toNNReal =
      ν.restrict {z : upperHalfPlane | (z:ℂ) ∈ γ '' Icc 0 (q:ℝ).toNNReal}) :
    ∀ t, N t = ν.restrict {z : upperHalfPlane | (z:ℂ) ∈ γ '' Icc 0 t} := by
  intro t
  let A : Set upperHalfPlane := {z | (z:ℂ) ∈ γ '' Icc 0 t}
  have hA : MeasurableSet A :=
    ((isCompact_Icc.image hγ).isClosed.preimage continuous_subtype_val).measurableSet
  have hNpast : (N t).restrict A = N t := by
    apply Measure.restrict_eq_self_of_ae_mem
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp (hpast t)] with z hz
    exact not_not.mp hz
  let D := localTestFamily upperHalfPlane
  have hcover : ⋃ n, D.compactSet n = univ := by
    apply eq_univ_of_forall
    intro z
    obtain ⟨n,hn⟩ := D.exhaustive {z} isCompact_singleton
    exact mem_iUnion.mpr ⟨n,hn (mem_singleton z)⟩
  apply Measure.ext_of_iUnion_eq_univ hcover
  intro n
  apply Measure.ext
  intro E hE
  rw [Measure.restrict_apply hE,Measure.restrict_apply hE]
  have hEK : MeasurableSet (E ∩ D.compactSet n) := hE.inter (D.isCompact n).measurableSet
  rw [Measure.restrict_apply hEK]
  have hcut : N t (E ∩ D.compactSet n) = N t ((E ∩ D.compactSet n) ∩ A) := by
    conv_lhs => rw [← hNpast]
    rw [Measure.restrict_apply hEK]
  rw [hcut]
  let L := (E ∩ D.compactSet n) ∩ A
  have hL : MeasurableSet L := hEK.inter hA
  have hLK : L ⊆ D.compactSet n := fun _ hz => hz.1.2
  have hνfin : ν L ≠ ∞ := (lt_of_le_of_lt (measure_mono hLK) (D.isCompact n).measure_lt_top).ne
  have hNfin : N t L ≠ ∞ := (lt_of_le_of_lt (hp.dominated t L) (lt_top_iff_ne_top.mpr hνfin)).ne
  have heReal : (N t L).toReal = (ν L).toReal := by
    apply eq_of_forall_dist_le
    intro ε hε
    obtain ⟨δ,hδ,hvar⟩ := hp.local_variation (D.compactSet n) (D.isCompact n) t ε hε
    obtain ⟨q,htq,hqt⟩ := exists_rat_btwn (lt_add_of_pos_right (t:ℝ) hδ)
    have hq0 : 0 ≤ q := Rat.cast_nonneg.mp ((NNReal.coe_nonneg t).trans htq.le)
    have hqr : ((q:ℝ).toNNReal:ℝ) = q := Real.coe_toNNReal _ (Rat.cast_nonneg.mpr hq0)
    have htqNN : t ≤ (q:ℝ).toNNReal := by
      apply NNReal.coe_le_coe.mp
      rw [hqr]
      exact htq.le
    have hnear : dist (((q:ℝ).toNNReal):ℝ) t < δ := by
      rw [hqr,Real.dist_eq,abs_of_pos (sub_pos.mpr htq)]
      linarith
    have hvalues : N (q:ℝ).toNNReal L = ν L := by
      rw [hq q hq0,Measure.restrict_apply hL]
      congr 1
      apply inter_eq_left.mpr
      intro z hz
      exact image_mono (Icc_subset_Icc le_rfl htqNN) hz.2
    have hv := hvar t (q:ℝ).toNNReal (by simpa using hδ) hnear L hL hLK
    rw [hvalues] at hv
    exact le_of_lt (by simpa only [Real.dist_eq] using hv)
  calc
    N t L = ENNReal.ofReal (N t L).toReal := (ENNReal.ofReal_toReal hNfin).symm
    _ = ENNReal.ofReal (ν L).toReal := congrArg ENNReal.ofReal heReal
    _ = ν L := ENNReal.ofReal_toReal hνfin

end SLEExactGauge.Multipoint

end

end OAI
