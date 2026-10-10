import OAI.Probability.SLE.Mass.RationalTraceMassLocal
import OAI.Probability.SLE.Mass.LevelRadonSupport
import OAI.Probability.SLE.Mass.LocallyFiniteMeasureSubtract

namespace OAI

/-! Past support and the remaining-mass support give exactly the rational
increment hypothesis used by the locally finite continuous extension. -/

noncomputable section
open Set MeasureTheory Classical
open scoped NNReal ENNReal

namespace SLEExactGauge

local instance : LocallyCompactSpace upperHalfPlane := isOpen_upperHalfPlane.locallyCompactSpace

lemma trace_segment_toNNReal_image (γ : ℝ≥0 → ℂ) {p q : ℚ} (hp : 0 ≤ p) (hpq : p ≤ q) :
    γ '' Icc (p : ℝ).toNNReal (q : ℝ).toNNReal ⊆
      (fun r : ℝ => γ r.toNNReal) '' Icc (p:ℝ) q := by
  rintro _ ⟨r,hr,rfl⟩
  refine ⟨(r:ℝ),⟨?_,?_⟩,?_⟩
  · have hr' : ((p:ℝ).toNNReal:ℝ) ≤ (r:ℝ) := by exact_mod_cast hr.1
    simpa only [Real.coe_toNNReal _ (Rat.cast_nonneg.mpr hp)] using hr'
  · have hq : (0:ℝ) ≤ q := Rat.cast_nonneg.mpr (hp.trans hpq)
    have hr' : (r:ℝ) ≤ ((q:ℝ).toNNReal:ℝ) := by exact_mod_cast hr.2
    simpa only [Real.coe_toNNReal _ hq] using hr'
  · change γ (r:ℝ).toNNReal = γ r
    rw [Real.toNNReal_coe]

theorem halfPlaneTraceIncrements_of_past_and_future
    (μ : ℚ → Measure upperHalfPlane) (ν : Measure upperHalfPlane) [ν.Regular]
    (γ : ℝ≥0 → ℂ) (hμr : ∀ q, (μ q).Regular)
    (hdom : ∀ q, μ q ≤ ν) (hmono : Monotone μ)
    (hzero : ∀ q, q ≤ 0 → μ q = 0)
    (hpast : ∀ q, 0 ≤ q → μ q {z : upperHalfPlane | (z : ℂ) ∉ γ '' Icc 0 (q : ℝ).toNNReal} = 0)
    (hfuture : ∀ q, 0 ≤ q → (ν-μ q)
      {z : upperHalfPlane | (z : ℂ) ∉ survivingDomain γ (q : ℝ).toNNReal} = 0) :
    HalfPlaneTraceIncrements μ ν (fun r : ℝ => γ r.toNNReal) := by
  let (q : ℚ) : (μ q).Regular := hμr q
  refine ⟨hμr,hdom,?_⟩
  intro p q hpq
  let η := μ q-μ p
  have hηsum : μ q = μ p+η := by
    rw [add_comm]
    exact (sigmaFinite_sub_add_cancel_of_le (hmono hpq)).symm
  refine ⟨η,hηsum,?_⟩
  by_cases hq : q ≤ 0
  · have hp : p ≤ 0 := hpq.trans hq
    simp only [η,hzero p hp,hzero q hq,Measure.sub_self]
    exact bot_le
  by_cases hp : p < 0
  · have heη : η = μ q := by simp only [η,hzero p hp.le,Measure.sub_zero]
    rw [heη]
    let A := {z : upperHalfPlane | (z : ℂ) ∈ (fun r : ℝ => γ r.toNNReal) '' Icc (p:ℝ) q}
    have hqpos : 0 < (q:ℝ) := Rat.cast_pos.mpr (lt_of_not_ge hq)
    have hsubset : γ '' Icc 0 (q:ℝ).toNNReal ⊆
        (fun r : ℝ => γ r.toNNReal) '' Icc (p:ℝ) q := by
      rintro _ ⟨r,hr,rfl⟩
      refine ⟨(r:ℝ),⟨(Rat.cast_nonpos.mpr hp.le).trans r.coe_nonneg,?_⟩,?_⟩
      · have hr' : (r:ℝ) ≤ ((q:ℝ).toNNReal:ℝ) := by exact_mod_cast hr.2
        simpa only [Real.coe_toNNReal _ hqpos.le] using hr'
      · change γ (r:ℝ).toNNReal = γ r
        rw [Real.toNNReal_coe]
    have ha : ∀ᵐ z : upperHalfPlane ∂μ q, z ∈ A := by
      have hh := measure_eq_zero_iff_ae_notMem.mp (hpast q (lt_of_not_ge hq).le)
      filter_upwards [hh] with z hz
      exact hsubset (not_not.mp hz)
    calc
      μ q = (μ q).restrict A := (Measure.restrict_eq_self_of_ae_mem ha).symm
      _ ≤ ν.restrict A := Measure.restrict_mono le_rfl (hdom q)
  · have hp' : 0 ≤ p := le_of_not_gt hp
    have hq' : 0 ≤ q := hp'.trans hpq
    have hh := Multipoint.increment_le_restrict_trace_segment γ
      (p:ℝ).toNNReal (q:ℝ).toNNReal η (μ q) (ν-μ p) ν
      Measure.sub_le (sub_le_sub_right_of_le (hdom p) (hdom q))
      (Measure.sub_le.trans (hdom q)) (hpast q hq') (hfuture p hp')
    exact hh.trans (Measure.restrict_mono
      (fun (z : upperHalfPlane) hz => trace_segment_toNNReal_image γ hp' hpq hz) le_rfl)

end SLEExactGauge

end

end OAI
