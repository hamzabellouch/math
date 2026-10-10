import OAI.GroupTheory.Thompson.DyadicImages
import OAI.GroupTheory.Thompson.IntervalCharts
import OAI.GroupTheory.Thompson.StandardF

namespace OAI

/-!
# Exact covariance under actual affine transport

Every source image cell and its target image cell retain the same original
uniform-grid index. The affine chart equality therefore identifies the
normalized restrictions pointwise, including their closed endpoints.
-/

namespace ThompsonNonamenability

namespace CarriesAffinely

theorem chart_value_eq_iff {h : F} {I J : BasicInterval}
    (hc : CarriesAffinely h I J) (x y : UnitInterval) :
    (h x : ℝ) = J.chart (y : ℝ) ↔ (x : ℝ) = I.chart (y : ℝ) := by
  constructor
  · intro hx
    have heq : h x = h (I.chartPoint y) :=
      Subtype.ext (hx.trans (hc y).symm)
    exact congrArg (fun z : UnitInterval => (z : ℝ)) (h.strictMono.injective heq)
  · intro hx
    have heq : x = I.chartPoint y := Subtype.ext hx
    rw [heq]
    exact hc y

theorem left_value_eq_iff {h : F} {I J : BasicInterval}
    (hc : CarriesAffinely h I J) (x : UnitInterval) :
    (h x : ℝ) = J.left ↔ (x : ℝ) = I.left := by
  simpa only [coe_unitIntervalZero, BasicInterval.chart_zero] using
    hc.chart_value_eq_iff x unitIntervalZero

theorem right_value_eq_iff {h : F} {I J : BasicInterval}
    (hc : CarriesAffinely h I J) (x : UnitInterval) :
    (h x : ℝ) = J.right ↔ (x : ℝ) = I.right := by
  simpa only [coe_unitIntervalOne, BasicInterval.chart_one] using
    hc.chart_value_eq_iff x unitIntervalOne

end CarriesAffinely

/-- Corresponding actual image cells have exactly the affinely transported
endpoints. No admissibility of any other interval is assumed here. -/
theorem imageCell_transport_iff (h g : F) (n : ℕ)
    (I I' : BasicInterval) (hc : CarriesAffinely h I I')
    (hg : ImageBasic g n) (hhg : ImageBasic (h * g) n) (k : Fin (2 ^ n)) :
    imageCell (h * g) n hhg k = I' ↔ imageCell g n hg k = I := by
  constructor
  · intro heq
    apply BasicInterval.ext_endpoints
    · have hl := congrArg BasicInterval.left heq
      simp only [imageCell_left, F.mul_apply] at hl
      rw [imageCell_left]
      exact (hc.left_value_eq_iff _).mp hl
    · have hr := congrArg BasicInterval.right heq
      simp only [imageCell_right, F.mul_apply] at hr
      rw [imageCell_right]
      exact (hc.right_value_eq_iff _).mp hr
  · intro heq
    apply BasicInterval.ext_endpoints
    · have hl := congrArg BasicInterval.left heq
      simp only [imageCell_left] at hl
      rw [imageCell_left, F.mul_apply]
      exact (hc.left_value_eq_iff _).mpr hl
    · have hr := congrArg BasicInterval.right heq
      simp only [imageCell_right] at hr
      rw [imageCell_right, F.mul_apply]
      exact (hc.right_value_eq_iff _).mpr hr

/-- Exact normalized restriction covariance for multiplication `h * g = h ∘ g`. -/
theorem image_restrict_covariance
    (h g : F) (n : ℕ) (I I' : BasicInterval)
    (hc : CarriesAffinely h I I')
    (hg : ImageBasic g n) (hhg : ImageBasic (h * g) n)
    (hr : (imagePartition g n hg).Respects I)
    (hr' : (imagePartition (h * g) n hhg).Respects I') :
    (imagePartition (h * g) n hhg).restrict I' hr' =
      (imagePartition g n hg).restrict I hr := by
  apply BasicPartition.ext
  ext K
  simp only [BasicPartition.mem_restrict_cells, mem_imagePartition_cells]
  constructor
  · rintro ⟨k, hk⟩
    exact ⟨k, (imageCell_transport_iff h g n (I.comp K) (I'.comp K)
      (hc.comp K) hg hhg k).mp hk⟩
  · rintro ⟨k, hk⟩
    exact ⟨k, (imageCell_transport_iff h g n (I.comp K) (I'.comp K)
      (hc.comp K) hg hhg k).mpr hk⟩

end ThompsonNonamenability

end OAI
