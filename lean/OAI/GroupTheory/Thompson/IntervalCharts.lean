import OAI.GroupTheory.Thompson.BasicInterval
import OAI.GroupTheory.Thompson.StandardPL

namespace OAI

/-!
# Actual affine charts of basic intervals

The chart is bundled as a point of the real unit interval. Affine transport
means equality of these actual maps at every point, including both endpoints.
-/

noncomputable section

namespace ThompsonNonamenability

namespace BasicInterval

def chartPoint (I : BasicInterval) (x : UnitInterval) : UnitInterval :=
  ⟨I.chart (x : ℝ), I.carrier_subset_unit
    ((I.chart_mem_self_carrier_iff (x : ℝ)).mpr x.property)⟩

@[simp] theorem coe_chartPoint (I : BasicInterval) (x : UnitInterval) :
    (I.chartPoint x : ℝ) = I.chart (x : ℝ) := rfl

theorem chartPoint_injective (I : BasicInterval) :
    Function.Injective I.chartPoint := by
  intro x y h
  apply Subtype.ext
  exact I.chart_injective (congrArg (fun z : UnitInterval => (z : ℝ)) h)

@[simp] theorem chartPoint_comp (I J : BasicInterval) (x : UnitInterval) :
    (I.comp J).chartPoint x = I.chartPoint (J.chartPoint x) := by
  apply Subtype.ext
  exact I.chart_comp J (x : ℝ)

theorem chartPoint_mem_carrier (I : BasicInterval) (x : UnitInterval) :
    (I.chartPoint x : ℝ) ∈ I.carrier :=
  (I.chart_mem_self_carrier_iff (x : ℝ)).mpr x.property

theorem exists_chartPoint (I : BasicInterval) (x : UnitInterval)
    (hx : (x : ℝ) ∈ I.carrier) : ∃ y : UnitInterval, I.chartPoint y = x := by
  let t : ℝ := ((x : ℝ) - I.left) / I.length
  have ht : t ∈ Set.Icc (0 : ℝ) 1 := by
    constructor
    · exact div_nonneg (sub_nonneg.mpr hx.1) I.length_pos.le
    · apply (div_le_one I.length_pos).mpr
      rw [I.length_eq_right_sub_left]
      exact sub_le_sub_right hx.2 _
  refine ⟨⟨t, ht⟩, ?_⟩
  apply Subtype.ext
  change I.chart t = (x : ℝ)
  rw [I.chart_eq_left_add_length_mul]
  dsimp [t]
  field_simp [ne_of_gt I.length_pos]
  ring

theorem left_isDyadic (I : BasicInterval) : IsDyadic I.left := by
  exact ⟨(I.index.val : ℤ), I.depth, by simp only [left, Int.cast_natCast]⟩

theorem right_isDyadic (I : BasicInterval) : IsDyadic I.right := by
  exact ⟨(I.index.val : ℤ) + 1, I.depth, by
    simp only [right, Int.cast_add, Int.cast_natCast, Int.cast_one]⟩

end BasicInterval

def CarriesAffinely (h : F) (I J : BasicInterval) : Prop :=
  ∀ x : UnitInterval, (h (I.chartPoint x) : ℝ) = J.chart (x : ℝ)

namespace CarriesAffinely

theorem chartPoint {h : F} {I J : BasicInterval} (hc : CarriesAffinely h I J)
    (x : UnitInterval) : h (I.chartPoint x) = J.chartPoint x :=
  Subtype.ext (hc x)

theorem comp {h : F} {I J : BasicInterval} (hc : CarriesAffinely h I J)
    (K : BasicInterval) : CarriesAffinely h (I.comp K) (J.comp K) := by
  intro x
  simpa only [BasicInterval.chartPoint_comp, BasicInterval.chart_comp,
    BasicInterval.coe_chartPoint] using hc (K.chartPoint x)

theorem maps_carrier {h : F} {I J : BasicInterval} (hc : CarriesAffinely h I J)
    {x : UnitInterval} (hx : (x : ℝ) ∈ I.carrier) : (h x : ℝ) ∈ J.carrier := by
  obtain ⟨y, rfl⟩ := I.exists_chartPoint x hx
  rw [hc y]
  exact (J.chart_mem_self_carrier_iff (y : ℝ)).mpr y.property

theorem preimage_carrier {h : F} {I J : BasicInterval}
    (hc : CarriesAffinely h I J) {x : UnitInterval} :
    (h x : ℝ) ∈ J.carrier ↔ (x : ℝ) ∈ I.carrier := by
  constructor
  · intro hx
    obtain ⟨y, hy⟩ := J.exists_chartPoint (h x) hx
    have hxy : I.chartPoint y = x :=
      h.toHomeomorph.injective ((hc.chartPoint y).trans hy)
    rw [← hxy]
    exact I.chartPoint_mem_carrier y
  · exact hc.maps_carrier

end CarriesAffinely

end ThompsonNonamenability

end

end OAI
