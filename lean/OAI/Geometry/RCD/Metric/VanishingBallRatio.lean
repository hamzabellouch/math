import OAI.Geometry.RCD.Metric.LocalBallMeasureOrder

namespace OAI

/-! # A finite Euclidean measure cannot have zero ball density everywhere it lives -/

open Set Metric Filter MeasureTheory
open scoped Topology NNReal ENNReal
noncomputable section
namespace RegularPointCoordinates

theorem local_ball_measure_order_at {m : ℕ}
    (μ : Measure (Euclidean m)) [IsFiniteMeasure μ] (c : ℝ≥0)
    {A : Set (Euclidean m)}
    (hb : ∀ x ∈ A, ∃ R : ℝ, 0 < R ∧ ∀ r : ℝ, 0 < r → r ≤ R →
      μ (closedBall x r) ≤ (c:ℝ≥0∞)*volume (closedBall x r)) :
    μ A ≤ (c • volume) A := by
  apply (Besicovitch.vitaliFamily μ).measure_le_of_frequently_le (c • volume)
    Measure.AbsolutelyContinuous.rfl A
  intro x hx
  obtain ⟨R,hR,hbound⟩ := hb x hx
  rw [VitaliFamily.frequently_filterAt_iff]
  intro ε hε
  let r := min R ε
  have hr : 0 < r := lt_min hR hε
  refine ⟨closedBall x r,mem_image_of_mem _ hr,
    closedBall_subset_closedBall (min_le_right _ _),?_⟩
  simpa only [Measure.coe_nnreal_smul_apply] using hbound r hr (min_le_left _ _)

theorem measure_zero_of_vanishing_ball_ratio {m : ℕ}
    (μ : Measure (Euclidean m)) [IsFiniteMeasure μ] {A : Set (Euclidean m)}
    (hA : volume A ≠ ⊤)
    (hratio : ∀ x ∈ A, Tendsto (fun r => μ.real (closedBall x r) /
      volume.real (closedBall x r)) (𝓝[>] 0) (𝓝 0)) : μ A = 0 := by
  have hbound (c : ℝ≥0) (hc : 0 < c) : μ.real A ≤ (c:ℝ)*volume.real A := by
    have hh : μ A ≤ (c • volume) A := by
      apply local_ball_measure_order_at μ c
      intro x hx
      have he := (hratio x hx).eventually (gt_mem_nhds (show (0:ℝ)<c from hc))
      obtain ⟨R,hR,hbound⟩ := Metric.mem_nhdsWithin_iff.mp he
      refine ⟨R/2,by positivity,?_⟩
      intro r hr hrR
      have hdr : dist r 0 < R := by rw [Real.dist_eq,sub_zero,abs_of_pos hr]; linarith
      have hv : 0 < volume.real (closedBall x r) :=
        ENNReal.toReal_pos (measure_closedBall_pos volume x hr).ne' measure_closedBall_lt_top.ne
      have hle : μ.real (closedBall x r) ≤ (c:ℝ)*volume.real (closedBall x r) :=
        (div_le_iff₀ hv).mp ((hbound ⟨hdr,hr⟩).le)
      apply (ENNReal.toReal_le_toReal (measure_ne_top μ _)
        (ENNReal.mul_ne_top ENNReal.coe_ne_top measure_closedBall_lt_top.ne)).mp
      simpa only [ENNReal.toReal_mul,ENNReal.coe_toReal,Measure.real] using hle
    have hreal := ENNReal.toReal_mono (by simpa using ENNReal.mul_ne_top ENNReal.coe_ne_top hA) hh
    simpa only [Measure.coe_nnreal_smul_apply,ENNReal.toReal_mul,ENNReal.coe_toReal,Measure.real] using hreal
  have hzero : μ.real A ≤ 0 := by
    have ht := tendsto_one_div_add_atTop_nhds_zero_nat.mul_const (volume.real A)
    simp only [zero_mul] at ht
    apply ge_of_tendsto ht
    exact Eventually.of_forall (fun k => hbound
      ⟨1/((k:ℝ)+1),by positivity⟩ (by
        change (0:ℝ) < 1/((k:ℝ)+1)
        positivity))
  have he : μ.real A = 0 := le_antisymm hzero measureReal_nonneg
  exact (measureReal_eq_zero_iff (measure_ne_top μ A)).mp he

end RegularPointCoordinates

end

end OAI
