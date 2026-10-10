import OAI.Probability.SLE.Loewner.SmoothRawFreshness
import OAI.Probability.SLE.Loewner.RawSurvivingAnalytic
import OAI.Probability.SLE.Loewner.SmoothRawTraceContinuous

namespace OAI

/-! Every positive-time raw tip is new: it survives all earlier times
and fails to survive its own time. Hence the smooth raw trace is simple. -/
noncomputable section
open Set Filter _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory
open scoped Topology NNReal

namespace SLEExactGauge

lemma Target.smooth_raw_tip_survives_past (b : Driver) (T S : ℝ≥0) (hST : S<T)
    (b' : ℝ → ℝ)
    (hd : ∀ t ∈ Icc 0 (T : ℝ), HasDerivWithinAt (driverValue b)
      (b' t) (Icc 0 (T : ℝ)) t)
    {L : ℝ} (hL : 0 ≤ L) (hb : ∀ t ∈ Icc 0 (T : ℝ), |b' t| ≤ L) :
    Surviving 1 b (trace 1 b T) S := by
  let ar : ℝ := min (((T : ℝ)-S)/2) (1/(L^2+1))
  have har : 0 < ar := lt_min (by exact half_pos (sub_pos.mpr hST)) (by positivity)
  let a : ℝ≥0 := ⟨ar,har.le⟩
  have ha0 : 0 < a := har
  have haT : a ≤ T := by
    change ar ≤ (T : ℝ)
    have hh : ar ≤ ((T : ℝ)-S)/2 := min_le_left _ _
    linarith [S.coe_nonneg,T.coe_nonneg]
  have hsmall : L^2*(a : ℝ) ≤ 1 := by
    have hh : ar*(L^2+1) ≤ 1 :=
      (le_div_iff₀ (show 0 < L^2+1 by positivity)).mp (min_le_right _ _)
    change L^2*ar ≤ 1
    nlinarith [har.le]
  have hpast : S ≤ T-a := by
    change (S : ℝ) ≤ ((T-a : ℝ≥0) : ℝ)
    rw [NNReal.coe_sub haT]
    have hh : ar ≤ ((T : ℝ)-S)/2 := min_le_left _ _
    change (S : ℝ) ≤ (T : ℝ)-ar
    linarith [show (S : ℝ)<T from hST]
  exact surviving_of_le_time 1 b _ S.coe_nonneg hpast
    (smooth_raw_tip_survives_short_past b T a haT ha0 b' hd hL hb hsmall)

theorem RegularSLEPresentation.smooth_raw_trace_injective
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {κ : ℝ} {γ : Ω → ℝ≥0 → ℂ} (a : RegularSLEPresentation P κ γ) (hκ : 0 < κ)
    (b : Target.Driver) (b' : ℝ → ℝ) (L : ℝ≥0)
    (hd : ∀ t, 0 ≤ t → HasDerivWithinAt (Target.driverValue b) (b' t) (Ici 0) t)
    (hb : ∀ t, 0 ≤ t → |b' t| ≤ L) :
    Function.Injective (fun T : ℝ≥0 => Target.trace 1 b T) := by
  have hdT (T : ℝ≥0) (t : ℝ) (ht : t ∈ Icc 0 (T : ℝ)) :=
    (hd t ht.1).mono (show Icc 0 (T : ℝ) ⊆ Ici 0 from Icc_subset_Ici_self)
  have hbT (T : ℝ≥0) (t : ℝ) (ht : t ∈ Icc 0 (T : ℝ)) := hb t ht.1
  intro S T he
  change Target.trace 1 b S=Target.trace 1 b T at he
  rcases lt_trichotomy S T with hST | heq | hTS
  · have hp := Target.smooth_raw_tip_survives_past b T S hST b' (hdT T) L.coe_nonneg (hbT T)
    rw [← he] at hp
    exact False.elim ((a.smooth_raw_tip_not_surviving hκ b S b' (hdT S) L.coe_nonneg (hbT S)) hp)
  · exact heq
  · have hp := Target.smooth_raw_tip_survives_past b S T hTS b' (hdT S) L.coe_nonneg (hbT S)
    rw [he] at hp
    exact False.elim ((a.smooth_raw_tip_not_surviving hκ b T b' (hdT T) L.coe_nonneg (hbT T)) hp)

end SLEExactGauge

end

end OAI
