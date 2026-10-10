import Mathlib
import OAI.Analysis.BiholderTransport.Volume.LocalJacobianBarrier

namespace OAI

section
section
noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

namespace WeakMTWTransport
section LowerTestContact
variable {X Y : Type*} [MetricSpace X] [ProperSpace X]

lemma lower_test_sublevel_contacts {v φ : X → ℝ} {c : X → Y → ℝ}
    {S : X → Y} {R : X → Y → Prop} {x : X} {r h : ℝ} (hr : 0 < r)
    (hv : ContinuousOn v (Metric.closedBall x r))
    (hc : ∀ y, ContinuousOn (fun w => c w y) (Metric.closedBall x r))
    (hboundary : ∀ w, dist w x=r → h ≤ v w-φ w)
    (hlocal : ∀ w∈Metric.ball x r, ∀ z∈Metric.ball x r,
      IsLocalMin (fun w => v w+c w (S z)) w → R w (S z))
    (hmountain : ∀ z∈Metric.ball x r, v z-φ z < h →
      ∀ w∈Metric.closedBall x r, φ z+c z (S z) ≤ φ w+c w (S z)) :
    ∀ z∈Metric.ball x r, v z-φ z < h →
      ∃ w∈Metric.ball x r, v w-φ w < h ∧ R w (S z) := by
  intro z hz hzgap
  have hzclosed : z∈Metric.closedBall x r := Metric.ball_subset_closedBall hz
  obtain ⟨w,hw,hmin⟩ := (isCompact_closedBall x r).exists_isMinOn
    (Metric.nonempty_closedBall.mpr hr.le) (hv.add (hc (S z)))
  have hvalue : v w+c w (S z) ≤ v z+c z (S z) := hmin hzclosed
  have hmount : φ z+c z (S z) ≤ φ w+c w (S z) := hmountain z hz hzgap w hw
  have hwgap : v w-φ w < h := by linarith only [hvalue,hmount,hzgap]
  have hwin : w∈Metric.ball x r := by
    apply lt_of_le_of_ne (Metric.mem_closedBall.mp hw)
    intro he
    exact (not_le_of_gt hwgap) (hboundary w he)
  refine ⟨w,hwin,hwgap,hlocal w hwin z hz ?_⟩
  exact hmin.isLocalMin (Metric.closedBall_mem_nhds_of_mem hwin)

end LowerTestContact
end WeakMTWTransport

end

end

section

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

namespace WeakMTWTransport
section LowerTestViscosity
variable {E Y : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  (μ : Measure E) [μ.IsAddHaarMeasure]

lemma lower_test_abs_det_le {v φ : E → ℝ} {c : E → E → ℝ}
    {S : E → E} {R : E → E → Prop} {x : E} {r₀ ε C : ℝ}
    {A : E →L[ℝ] E} (hr₀ : 0 < r₀) (hε : 0 < ε) (hC : 0 ≤ C)
    (hv : ContinuousOn v (Metric.closedBall x r₀))
    (hφ : ContinuousOn φ (Metric.closedBall x r₀))
    (hc : ∀ y, ContinuousOn (fun w => c w y) (Metric.closedBall x r₀))
    (hx : v x=φ x)
    (hgap : ∀ w∈Metric.closedBall x r₀, ε*dist w x^2 ≤ v w-φ w)
    (hlocal : ∀ w∈Metric.ball x r₀, ∀ z∈Metric.ball x r₀,
      IsLocalMin (fun w => v w+c w (S z)) w → R w (S z))
    (hmountain : ∀ z∈Metric.ball x r₀, ∀ w∈Metric.closedBall x r₀,
      φ z+c z (S z) ≤ φ w+c w (S z))
    (hvol : ∀ s : Set E, MeasurableSet s → s⊆Metric.ball x r₀ →
      μ {y | ∃ w∈s, R w y} ≤ ENNReal.ofReal C*μ s)
    (hS : HasStrictFDerivAt S A x) : |A.det| ≤ C := by
  apply abs_det_le_of_small_image_bounds μ hS hC
  intro U hU
  obtain ⟨r,hr,hrU⟩ := Metric.nhds_basis_closedBall.mem_iff.mp
    (inter_mem hU (Metric.ball_mem_nhds x hr₀))
  have hrsub : Metric.closedBall x r ⊆ Metric.closedBall x r₀ :=
    fun w hw => Metric.ball_subset_closedBall (hrU hw).2
  have hrb : Metric.ball x r ⊆ Metric.ball x r₀ :=
    fun w hw => (hrU (Metric.ball_subset_closedBall hw)).2
  let h := ε*r^2/2
  have hh : 0 < h := by dsimp [h]; positivity
  let Ω : Set E := Metric.ball x r ∩ {w | v w-φ w < h}
  have hΩopen : IsOpen Ω :=
    ((hv.sub hφ).mono (fun w hw => hrsub (Metric.ball_subset_closedBall hw))).isOpen_inter_preimage
      Metric.isOpen_ball isOpen_Iio
  have hxΩ : x∈Ω := by
    exact ⟨Metric.mem_ball_self hr,by change v x-φ x < h; simpa only [hx,sub_self] using hh⟩
  have hΩsub : Ω⊆Metric.ball x r₀ := fun w hw => hrb hw.1
  have hcontact : S '' Ω ⊆ {y | ∃ w∈Ω, R w y} := by
    rintro y ⟨z,hz,rfl⟩
    obtain ⟨w,hw,hwh,hwR⟩ := lower_test_sublevel_contacts hr
      (hv.mono hrsub) (fun y => (hc y).mono hrsub) (h := h)
      (fun w he => by
        have H := hgap w (hrsub (Metric.mem_closedBall.mpr he.le))
        rw [he] at H
        have H' : ε*r^2/2 ≤ ε*r^2 := by nlinarith only [mul_nonneg hε.le (sq_nonneg r)]
        exact H'.trans H)
      (fun w hw z hz => hlocal w (hrb hw) z (hrb hz))
      (fun z hz _ w hw => hmountain z (hrb hz) w (hrsub hw)) z hz.1 hz.2
    exact ⟨w,⟨hw,hwh⟩,hwR⟩
  refine ⟨Ω,fun w hw => (hrU (Metric.ball_subset_closedBall hw.1)).1,
    (hΩopen.measure_pos μ ⟨x,hxΩ⟩).ne',?_,?_⟩
  · exact ne_top_of_le_ne_top (isCompact_closedBall x r).measure_lt_top.ne
      (measure_mono (fun w hw => Metric.ball_subset_closedBall hw.1))
  · exact (measure_mono hcontact).trans (hvol Ω hΩopen.measurableSet hΩsub)

end LowerTestViscosity
end WeakMTWTransport

end

end

end

end OAI
