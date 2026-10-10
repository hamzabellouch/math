import OAI.Analysis.CircleDomains.Probability.BandMeasure
import OAI.Analysis.CircleDomains.Probability.RandomShifts
import Mathlib.GroupTheory.QuotientGroup.ModEq

namespace OAI

/-!
# Actual probabilities that a shifted lattice meets a band

A grid of spacing `h` meets `[a,b]` exactly when the shift modulo `h`
lies in the projection of this interval. Haar measure of that projection
is at most `min h (b-a)`. Under the actual normalized interval law for
the shift, the probability is at most `min 1 ((b-a)/h)`.
-/

open Set MeasureTheory Metric

namespace CircleDomainRigidity.FiniteTransfer

def latticeBandIncidence (h a b : ℝ) : Set ℝ :=
  {θ | ∃ k : ℤ, θ + (k : ℝ) * h ∈ Icc a b}

theorem addCircle_eq_iff_exists_int (h a b : ℝ) :
    (a : AddCircle h) = (b : AddCircle h) ↔ ∃ k : ℤ, a = b + (k : ℝ) * h := by
  rw [← AddCommGroup.modEq_iff_eq_mod_zmultiples, AddCommGroup.modEq_comm,
    AddCommGroup.modEq_iff_eq_add_zsmul]
  simp only [zsmul_eq_mul]

theorem latticeBandIncidence_eq_preimage (h a b : ℝ) :
    latticeBandIncidence h a b =
      ((↑) : ℝ → AddCircle h) ⁻¹' (((↑) : ℝ → AddCircle h) '' Icc a b) := by
  ext θ
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨θ + (k : ℝ) * h, hk, ?_⟩
    exact (addCircle_eq_iff_exists_int h _ _).mpr ⟨k, rfl⟩
  · rintro ⟨x, hx, heq⟩
    obtain ⟨k, hk⟩ := (addCircle_eq_iff_exists_int h x θ).mp heq
    exact ⟨k, hk ▸ hx⟩

theorem measurableSet_latticeBandIncidence {h : ℝ} (hh : 0 < h) (a b : ℝ) :
    MeasurableSet (latticeBandIncidence h a b) := by
  let : Fact (0 < h) := ⟨hh⟩
  rw [latticeBandIncidence_eq_preimage]
  exact ((isCompact_Icc.image (AddCircle.continuous_mk' h)).isClosed.measurableSet).preimage
    (AddCircle.continuous_mk' h).measurable

theorem volume_addCircle_interval_le {h : ℝ} [Fact (0 < h)] (a b : ℝ) :
    volume (((↑) : ℝ → AddCircle h) '' Icc a b) ≤
      ENNReal.ofReal (min h (b - a)) := by
  have hsub : ((↑) : ℝ → AddCircle h) '' Icc a b ⊆
      closedBall (((a + b) / 2 : ℝ) : AddCircle h) ((b - a) / 2) := by
    rintro _ ⟨x, hx, rfl⟩
    rw [mem_closedBall, dist_eq_norm, ← QuotientAddGroup.mk_sub]
    apply QuotientAddGroup.norm_mk_le_norm.trans
    rw [Real.norm_eq_abs, abs_le]
    constructor <;> linarith [hx.1, hx.2]
  calc
    _ ≤ volume (closedBall (((a + b) / 2 : ℝ) : AddCircle h) ((b - a) / 2)) :=
      measure_mono hsub
    _ = _ := by rw [AddCircle.volume_closedBall]; congr 2; ring

/-- The normalized interval shift law gives the exact quotient measure
of the event, divided by the grid spacing. -/
theorem shiftLaw_latticeBandIncidence_eq {h : ℝ} [Fact (0 < h)] (a b : ℝ) :
    shiftLaw h (latticeBandIncidence h a b) =
      volume (((↑) : ℝ → AddCircle h) '' Icc a b) / ENNReal.ofReal h := by
  have hmeas : MeasurableSet (((↑) : ℝ → AddCircle h) '' Icc a b) :=
    (isCompact_Icc.image (AddCircle.continuous_mk' h)).isClosed.measurableSet
  have hpush := (AddCircle.measurePreserving_mk (T := h) 0).measure_preimage
    hmeas.nullMeasurableSet
  change (volume.restrict (Ioc 0 (0 + h)))
    (((↑) : ℝ → AddCircle h) ⁻¹' (((↑) : ℝ → AddCircle h) '' Icc a b)) = _ at hpush
  rw [shiftLaw_eq, Measure.smul_apply, smul_eq_mul,
    ← restrict_Ioc_eq_restrict_Icc, latticeBandIncidence_eq_preimage]
  rw [zero_add] at hpush
  rw [hpush, div_eq_mul_inv, mul_comm]

/-- The quantitative band-hit estimate used in the terminal-count
expectation. It is proved for the actual normalized shift measure. -/
theorem shiftLaw_latticeBandIncidence_le {h : ℝ} (hh : 0 < h) (a b : ℝ) :
    shiftLaw h (latticeBandIncidence h a b) ≤
      ENNReal.ofReal (min 1 ((b - a) / h)) := by
  let : Fact (0 < h) := ⟨hh⟩
  rw [shiftLaw_latticeBandIncidence_eq]
  calc
    _ ≤ ENNReal.ofReal (min h (b - a)) / ENNReal.ofReal h :=
      ENNReal.div_le_div_right (volume_addCircle_interval_le a b) _
    _ = ENNReal.ofReal (min h (b - a) / h) := (ENNReal.ofReal_div_of_pos hh).symm
    _ = _ := by rw [← min_div_div_right hh.le, div_self hh.ne']

end CircleDomainRigidity.FiniteTransfer

end OAI
