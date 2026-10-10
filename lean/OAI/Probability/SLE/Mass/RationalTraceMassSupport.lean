import OAI.Probability.SLE.Mass.RationalTraceMassLocal
import OAI.Probability.SLE.Mass.RadonTestLimitProperties
import OAI.Probability.SLE.Mass.LocallyFiniteMeasureSubtract

namespace OAI

/-! The trace support of rational increments passes simultaneously to every
real interval, using only monotonicity and continuity of the trace. -/

noncomputable section
open Set Filter MeasureTheory Classical
open scoped Topology ENNReal CompactlySupported

namespace SLEExactGauge

local instance : LocallyCompactSpace upperHalfPlane := isOpen_upperHalfPlane.locallyCompactSpace

lemma exists_rational_trace_enclosure_avoiding
    (γ : ℝ → ℂ) (hγ : Continuous γ) {s t : ℝ} (hst : s ≤ t)
    (K : Set ℂ) (hK : IsClosed K) (hdis : Disjoint K (γ '' Icc s t)) :
    ∃ p q : ℚ, (p:ℝ) < s ∧ t < (q:ℝ) ∧ Disjoint K (γ '' Icc (p:ℝ) q) := by
  let U := γ ⁻¹' Kᶜ
  have hU : IsOpen U := hK.isOpen_compl.preimage hγ
  have hs : s ∈ U := by
    intro hs
    exact Set.disjoint_left.mp hdis hs ⟨s,⟨le_rfl,hst⟩,rfl⟩
  have ht : t ∈ U := by
    intro ht
    exact Set.disjoint_left.mp hdis ht ⟨t,⟨hst,le_rfl⟩,rfl⟩
  obtain ⟨ε,hε,hballε⟩ := Metric.isOpen_iff.mp hU s hs
  obtain ⟨δ,hδ,hballδ⟩ := Metric.isOpen_iff.mp hU t ht
  obtain ⟨p,hp,hps⟩ := exists_rat_btwn (show s-ε < s by linarith)
  obtain ⟨q,htq,hq⟩ := exists_rat_btwn (show t < t+δ by linarith)
  refine ⟨p,q,hps,htq,Set.disjoint_left.mpr ?_⟩
  rintro z hz ⟨r,hr,rfl⟩
  by_cases hrs : r < s
  · have hb : r ∈ Metric.ball s ε := by
      rw [Metric.mem_ball,Real.dist_eq,abs_of_neg (sub_neg.mpr hrs)]
      linarith [hr.1]
    exact hballε hb hz
  by_cases htr : t < r
  · have hb : r ∈ Metric.ball t δ := by
      rw [Metric.mem_ball,Real.dist_eq,abs_of_pos (sub_pos.mpr htr)]
      linarith [hr.2]
    exact hballδ hb hz
  exact Set.disjoint_left.mp hdis hz ⟨r,⟨le_of_not_gt hrs,le_of_not_gt htr⟩,rfl⟩

theorem HalfPlaneTraceIncrements.extension_increment_carried
    {μ : ℚ → Measure upperHalfPlane} {ν : Measure upperHalfPlane} [ν.Regular]
    {γ : ℝ → ℂ} (H : HalfPlaneTraceIncrements μ ν γ) (hγ : Continuous γ)
    (M : ℝ → Measure upperHalfPlane) (hMr : ∀ t, (M t).Regular)
    (hrat : ∀ q : ℚ, M q = μ q) (hmono : Monotone M)
    {s t : ℝ} (hst : s ≤ t) :
    (M t-M s) {z : upperHalfPlane | (z:ℂ) ∉ γ '' Icc s t} = 0 := by
  let η := M t-M s
  let : (M t).Regular := hMr t
  let : (M s).Regular := hMr s
  let : IsFiniteMeasureOnCompacts η :=
    ⟨fun K hK => lt_of_le_of_lt (Measure.sub_le K) hK.measure_lt_top⟩
  let : η.Regular := inferInstance
  let S : Set upperHalfPlane := {z | (z:ℂ) ∈ γ '' Icc s t}
  apply radon_limit_carried_by_closed (fun _ => η) η (fun _ => tendsto_const_nhds) S
    (((isCompact_Icc.image hγ).isClosed).preimage continuous_subtype_val)
  intro f hf
  let K := (Subtype.val : upperHalfPlane → ℂ) '' tsupport f
  have hK : IsCompact K := f.hasCompactSupport.image continuous_subtype_val
  have hdis : Disjoint K (γ '' Icc s t) := by
    apply Set.disjoint_left.mpr
    rintro _ ⟨z,hz,rfl⟩ hs
    exact hf hz hs
  obtain ⟨p,q,hps,htq,havoid⟩ := exists_rational_trace_enclosure_avoiding γ hγ hst K hK.isClosed hdis
  have hpq : p ≤ q := Rat.cast_le.mp (hps.le.trans (hst.trans htq.le))
  obtain ⟨ξ,hξ,hξle⟩ := H.increment p q hpq
  have hηξ : η ≤ ξ := by
    apply Measure.sub_le_of_le_add
    calc
      M t ≤ M q := hmono htq.le
      _ = μ q := hrat q
      _ = μ p+ξ := hξ
      _ = ξ+M p := by rw [hrat p,add_comm]
      _ ≤ ξ+M s := add_le_add le_rfl (hmono hps.le)
  have hzero : η (tsupport f) = 0 := by
    apply le_zero_iff.mp
    apply ((hηξ _).trans (hξle _)).trans_eq
    rw [Measure.restrict_apply f.hasCompactSupport.measurableSet]
    have hempty : tsupport f ∩ {z : upperHalfPlane | (z:ℂ) ∈ γ '' Icc (p:ℝ) q} = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro z hz
      exact Set.disjoint_left.mp havoid ⟨z,hz.1,rfl⟩ hz.2
    rw [hempty,measure_empty]
  apply Eventually.of_forall
  intro _
  apply integral_eq_zero_of_ae
  filter_upwards [measure_eq_zero_iff_ae_notMem.mp hzero] with z hz
  exact image_eq_zero_of_notMem_tsupport hz

end SLEExactGauge

end

end OAI
