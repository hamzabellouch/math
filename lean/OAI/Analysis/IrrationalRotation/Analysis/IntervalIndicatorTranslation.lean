import Mathlib

namespace OAI

open Set MeasureTheory

namespace Invariant233.IntervalIndicatorTranslation

theorem differing_membership_subset_strips {a b t η : ℝ} (hη : 0 ≤ η)
    (ht : |t| ≤ η) :
    {x : ℝ | x ∈ Ico 0 1 ∧
        ¬ (Int.fract (x - t) ∈ Icc a b ↔ x ∈ Icc a b)} ⊆
      Icc 0 η ∪ Icc (1 - η) 1 ∪ Icc (a - η) (a + η) ∪ Icc (b - η) (b + η) := by
  intro x hx
  by_contra hn
  have ht' := abs_le.mp ht
  have hx0 := hx.1.1
  have hx1 := hx.1.2
  have hn0 : x ∉ Icc 0 η := by exact fun h => hn (Or.inl (Or.inl (Or.inl h)))
  have hn1 : x ∉ Icc (1 - η) 1 := by exact fun h => hn (Or.inl (Or.inl (Or.inr h)))
  have hna : x ∉ Icc (a - η) (a + η) := by exact fun h => hn (Or.inl (Or.inr h))
  have hnb : x ∉ Icc (b - η) (b + η) := by exact fun h => hn (Or.inr h)
  have hxη : η < x := by
    by_contra h
    exact hn0 ⟨hx0, le_of_not_gt h⟩
  have hxη' : x < 1 - η := by
    by_contra h
    exact hn1 ⟨le_of_not_gt h, hx1.le⟩
  have hfract : Int.fract (x - t) = x - t := by
    apply Int.fract_eq_self.mpr
    constructor <;> linarith
  apply hx.2
  rw [hfract]
  constructor
  · intro hxt
    constructor
    · by_contra h
      apply hna
      constructor <;> linarith [hxt.1]
    · by_contra h
      apply hnb
      constructor <;> linarith [hxt.2]
  · intro hxI
    constructor
    · by_contra h
      apply hna
      constructor <;> linarith [hxI.1]
    · by_contra h
      apply hnb
      constructor <;> linarith [hxI.2]

theorem measure_differing_membership_le {a b t η : ℝ} (hη : 0 ≤ η) (ht : |t| ≤ η) :
    volume.real {x : ℝ | x ∈ Ico 0 1 ∧
      ¬ (Int.fract (x - t) ∈ Icc a b ↔ x ∈ Icc a b)} ≤ 6 * η := by
  have hfinite : volume (Icc (0 : ℝ) η ∪ Icc (1 - η) 1 ∪
      Icc (a - η) (a + η) ∪ Icc (b - η) (b + η)) ≠ ⊤ :=
    (((isCompact_Icc.union isCompact_Icc).union isCompact_Icc).union isCompact_Icc).measure_ne_top
  calc
    _ ≤ volume.real (Icc (0 : ℝ) η ∪ Icc (1 - η) 1 ∪
        Icc (a - η) (a + η) ∪ Icc (b - η) (b + η)) :=
      measureReal_mono (differing_membership_subset_strips hη ht) hfinite
    _ ≤ (volume.real (Icc (0 : ℝ) η) + volume.real (Icc (1 - η) 1)) +
        volume.real (Icc (a - η) (a + η)) + volume.real (Icc (b - η) (b + η)) := by
      calc
        _ ≤ volume.real (Icc (0 : ℝ) η ∪ Icc (1 - η) 1 ∪ Icc (a - η) (a + η)) +
            volume.real (Icc (b - η) (b + η)) := measureReal_union_le _ _
        _ ≤ (volume.real (Icc (0 : ℝ) η ∪ Icc (1 - η) 1) +
            volume.real (Icc (a - η) (a + η))) + volume.real (Icc (b - η) (b + η)) :=
          by
            have h := measureReal_union_le (μ := volume)
              (Icc (0 : ℝ) η ∪ Icc (1 - η) 1) (Icc (a - η) (a + η))
            linarith
        _ ≤ _ := by
          have h := measureReal_union_le (μ := volume) (Icc (0 : ℝ) η) (Icc (1 - η) 1)
          linarith
    _ = 6 * η := by
      rw [Real.volume_real_Icc_of_le hη,
        Real.volume_real_Icc_of_le (show 1 - η ≤ (1 : ℝ) by linarith),
        Real.volume_real_Icc_of_le (show a - η ≤ a + η by linarith),
        Real.volume_real_Icc_of_le (show b - η ≤ b + η by linarith)]
      ring

theorem integral_indicator_translation_le {a b t η : ℝ} (hη : 0 ≤ η) (ht : |t| ≤ η) :
    (∫ x in (0 : ℝ)..1,
      |(Icc a b).indicator (fun _ => (1 : ℝ)) (Int.fract (x - t)) -
       (Icc a b).indicator (fun _ => (1 : ℝ)) (Int.fract x)|) ≤ 6 * η := by
  classical
  let s : Set ℝ := {x | ¬ (Int.fract (x - t) ∈ Icc a b ↔ x ∈ Icc a b)}
  have hs : MeasurableSet s := by
    apply MeasurableSet.compl
    exact (measurableSet_Icc.preimage (measurable_fract.comp (measurable_id.sub_const t))).iff
      measurableSet_Icc
  have heq : (∫ x in (0 : ℝ)..1,
      |(Icc a b).indicator (fun _ => (1 : ℝ)) (Int.fract (x - t)) -
       (Icc a b).indicator (fun _ => (1 : ℝ)) (Int.fract x)|) =
      ∫ x in (0 : ℝ)..1, s.indicator (fun _ => (1 : ℝ)) x := by
    apply intervalIntegral.integral_congr_Ioo_of_le (by norm_num)
    intro x hx
    dsimp only
    rw [Int.fract_eq_self.mpr ⟨hx.1.le, hx.2⟩]
    simp only [Set.indicator_apply, s, Set.mem_ofPred_eq]
    by_cases h1 : Int.fract (x - t) ∈ Icc a b <;>
      by_cases h2 : x ∈ Icc a b <;> simp [h1, h2]
  rw [heq, intervalIntegral.integral_of_le (by norm_num),
    ← integral_Ico_eq_integral_Ioc, integral_indicator_const 1 hs, measureReal_restrict_apply hs]
  simp only [smul_eq_mul, mul_one]
  have hset : s ∩ Ico 0 1 = {x : ℝ | x ∈ Ico 0 1 ∧
      ¬ (Int.fract (x - t) ∈ Icc a b ↔ x ∈ Icc a b)} := by
    ext x
    exact and_comm
  rw [hset]
  exact measure_differing_membership_le hη ht

theorem circle_integral_indicator_translation_le {a b t η : ℝ}
    (hη : 0 ≤ η) (ht : |t| ≤ η) :
    (∫ x : UnitAddCircle,
      |(Icc a b).indicator (fun _ => (1 : ℝ))
          (AddCircle.equivIco (1 : ℝ) 0 (x - (t : UnitAddCircle)) : ℝ) -
       (Icc a b).indicator (fun _ => (1 : ℝ))
          (AddCircle.equivIco (1 : ℝ) 0 x : ℝ)|) ≤ 6 * η := by
  have h := UnitAddCircle.intervalIntegral_preimage 0 (fun x : UnitAddCircle =>
      |(Icc a b).indicator (fun _ => (1 : ℝ))
          (AddCircle.equivIco (1 : ℝ) 0 (x - (t : UnitAddCircle)) : ℝ) -
       (Icc a b).indicator (fun _ => (1 : ℝ))
          (AddCircle.equivIco (1 : ℝ) 0 x : ℝ)|)
  rw [← h]
  have heq (x : ℝ) :
      (AddCircle.equivIco (1 : ℝ) 0 ((x : UnitAddCircle) - (t : UnitAddCircle)) : ℝ) =
        Int.fract (x - t) := by
    rw [← AddCircle.coe_sub]
    simpa using AddCircle.coe_equivIco_mk_apply (p := (1 : ℝ)) (x - t)
  have heq' (x : ℝ) : (AddCircle.equivIco (1 : ℝ) 0 (x : UnitAddCircle) : ℝ) =
      Int.fract x := by
    simp
  simpa only [zero_add, heq, heq'] using integral_indicator_translation_le hη ht

theorem circle_integral_indicator_translation_le_of_min {a b t η : ℝ}
    (hη : 0 ≤ η) (ht : t ∈ Icc (0 : ℝ) 1) (hnear : min t (1 - t) ≤ η) :
    (∫ x : UnitAddCircle,
      |(Icc a b).indicator (fun _ => (1 : ℝ))
          (AddCircle.equivIco (1 : ℝ) 0 (x - (t : UnitAddCircle)) : ℝ) -
       (Icc a b).indicator (fun _ => (1 : ℝ))
          (AddCircle.equivIco (1 : ℝ) 0 x : ℝ)|) ≤ 6 * η := by
  rcases min_le_iff.mp hnear with hleft | hright
  · exact circle_integral_indicator_translation_le hη (by rwa [abs_of_nonneg ht.1])
  · have h := circle_integral_indicator_translation_le (a := a) (b := b) hη
      (t := t - 1) (by rwa [abs_of_nonpos (by linarith [ht.2]), neg_sub])
    simpa only [AddCircle.coe_sub, AddCircle.coe_period, sub_zero] using h

end Invariant233.IntervalIndicatorTranslation

end OAI
