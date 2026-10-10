import OAI.MeasureTheory.Falconer.Geometry.FrequencyGeometry

namespace OAI

/-! # Ball bounds for an actual radial frequency-shell pushforward -/

namespace Falconer
open Set Metric MeasureTheory
open scoped ENNReal

noncomputable def radialFrequencyMap {d : ℕ} (z : ℝ × Sphere d) : Space d :=
  z.1 • (z.2 : Space d)

def radialFrequencyAnnulus (B : ℝ) : Set ℝ := {t | B ≤ |t| ∧ |t| ≤ 2*B}

noncomputable def radialFrequencyMeasure {d : ℕ} (ν : Measure (Sphere d)) (B : ℝ) :
    Measure (Space d) := Measure.map radialFrequencyMap
      ((volume.restrict (radialFrequencyAnnulus B)).prod ν)

def radialWindow (a r : ℝ) : Set ℝ := Ioo (a-r) (a+r) ∪ Ioo (-a-r) (-a+r)

theorem radialWindow_mem {a r t : ℝ} (h : |t| ∈ Ioo (a-r) (a+r)) :
    t ∈ radialWindow a r := by
  rcases le_total 0 t with ht | ht
  · left
    simpa only [abs_of_nonneg ht] using h
  · right
    rw [abs_of_nonpos ht] at h
    exact ⟨by linarith [h.2],by linarith [h.1]⟩

theorem radialWindow_volume {a r : ℝ} (hr : 0 ≤ r) :
    volume (radialWindow a r) ≤ ENNReal.ofReal (4*r) := by
  calc
    _ ≤ volume (Ioo (a-r) (a+r))+volume (Ioo (-a-r) (-a+r)) := measure_union_le _ _
    _ = ENNReal.ofReal (4*r) := by
      rw [Real.volume_Ioo,Real.volume_Ioo,← ENNReal.ofReal_add (by linarith) (by linarith)]
      congr 1
      ring

theorem radial_frequency_preimage {d : ℕ} {B r : ℝ} (hB : 0 < B) (_hr : 0 < r)
    (v : Space d) :
    radialFrequencyMap ⁻¹' ball v r ∩ (radialFrequencyAnnulus B ×ˢ (univ : Set (Sphere d))) ⊆
      radialWindow ‖v‖ r ×ˢ
        ({w : Sphere d | dist (w:Space d) (‖v‖⁻¹ • v) < 2*r/B} ∪
         {w : Sphere d | dist (w:Space d) (-‖v‖⁻¹ • v) < 2*r/B}) := by
  rintro ⟨t,w⟩ ⟨hball,hann⟩
  have hdist : ‖t • (w:Space d)-v‖ < r := by
    simpa only [mem_preimage,mem_ball,dist_eq_norm,radialFrequencyMap] using hball
  refine ⟨radialWindow_mem (radial_norm_interval (sphere_norm w) hdist),?_⟩
  by_cases hv : v = 0
  · left
    have ht : B < r := by
      have hh : |t| < r := by
        simpa only [hv,sub_zero,norm_smul,Real.norm_eq_abs,sphere_norm,mul_one] using hdist
      exact hann.1.1.trans_lt hh
    simp only [hv,norm_zero,inv_zero,zero_smul,dist_zero_right,sphere_norm,mem_ofPred_eq]
    apply (lt_div_iff₀ hB).mpr
    linarith
  · simpa only [dist_eq_norm,mem_union,mem_ofPred_eq,neg_smul] using
      radial_direction_close (sphere_norm w) hv hB hann.1.1 hdist

theorem radial_frequency_ball_bound {d : ℕ} (ν : Measure (Sphere d)) [IsFiniteMeasure ν]
    {B r δ L s : ℝ} (hB : 0 < B) (hr : 0 < r) (hL : 1 ≤ L) (hs : 0 ≤ s)
    (hmass : ν univ ≤ 1) (hscale : δ ≤ 2*r/B)
    (hball : ∀ x : Space d, ∀ a : ℝ, δ ≤ a → a ≤ 1 →
      ν {w : Sphere d | dist (w:Space d) x < a} ≤ ENNReal.ofReal (L*a^s))
    (v : Space d) :
    radialFrequencyMeasure ν B (ball v r) ≤ ENNReal.ofReal (8*r*L*(2*r/B)^s) := by
  let A := radialFrequencyAnnulus B
  let C := {w : Sphere d | dist (w:Space d) (‖v‖⁻¹ • v) < 2*r/B} ∪
    {w : Sphere d | dist (w:Space d) (-‖v‖⁻¹ • v) < 2*r/B}
  have hν : ν C ≤ 2*ENNReal.ofReal (L*(2*r/B)^s) := by
    calc
      _ ≤ ν {w : Sphere d | dist (w:Space d) (‖v‖⁻¹ • v) < 2*r/B}+
          ν {w : Sphere d | dist (w:Space d) (-‖v‖⁻¹ • v) < 2*r/B} := measure_union_le _ _
      _ ≤ ENNReal.ofReal (L*(2*r/B)^s)+ENNReal.ofReal (L*(2*r/B)^s) :=
        add_le_add (sphere_ball_bound_extended ν hmass hL hs hball _ hscale)
          (sphere_ball_bound_extended ν hmass hL hs hball _ hscale)
      _ = _ := (two_mul _).symm
  have hm : Measurable (@radialFrequencyMap d) := by unfold radialFrequencyMap; fun_prop
  rw [radialFrequencyMeasure,Measure.map_apply hm measurableSet_ball]
  have he : ((volume.restrict A).prod ν) (radialFrequencyMap ⁻¹' ball v r) =
      (volume.prod ν) ((radialFrequencyMap ⁻¹' ball v r) ∩ (A ×ˢ univ)) := by
    rw [Measure.restrict_prod_eq_prod_univ,Measure.restrict_apply (measurableSet_ball.preimage hm)]
  rw [he]
  calc
    _ ≤ (volume.prod ν) (radialWindow ‖v‖ r ×ˢ C) :=
      measure_mono (radial_frequency_preimage hB hr v)
    _ = volume (radialWindow ‖v‖ r)*ν C := Measure.prod_prod _ _
    _ ≤ ENNReal.ofReal (4*r)*(2*ENNReal.ofReal (L*(2*r/B)^s)) :=
      mul_le_mul' (radialWindow_volume hr.le) hν
    _ = _ := by
      rw [show (2:ℝ≥0∞) = ENNReal.ofReal (2:ℝ) by norm_num,
        ← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2),
        ← ENNReal.ofReal_mul (by positivity)]
      congr 1
      ring

end Falconer

end OAI
