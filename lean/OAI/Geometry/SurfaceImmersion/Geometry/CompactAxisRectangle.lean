import OAI.Geometry.SurfaceImmersion.Whitney.CompactArcTimeChart
import Mathlib.Topology.MetricSpace.Thickening

namespace OAI

/-! A compact axis segment in an open plane set has a uniform rectangular collar. -/
noncomputable section
open Set Filter Metric
open scoped Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

lemma open_interval_collar {a b : ℝ} (hab : a ≤ b) {U : Set ℝ}
    (hU : IsOpen U) (hI : Icc a b ⊆ U) :
    ∃ δ : ℝ, 0 < δ ∧ Icc (a-δ) (b+δ) ⊆ U := by
  obtain ⟨δ,hδ,hsub⟩ := isCompact_Icc.exists_cthickening_subset_open hU hI
  refine ⟨δ,hδ,?_⟩
  intro x hx
  apply hsub
  by_cases hxa : x < a
  · apply mem_cthickening_of_dist_le x a δ (Icc a b) ⟨le_rfl,hab⟩
    rw [Real.dist_eq,abs_of_nonpos (sub_nonpos.mpr hxa.le)]
    linarith [hx.1]
  · by_cases hbx : b < x
    · apply mem_cthickening_of_dist_le x b δ (Icc a b) ⟨hab,le_rfl⟩
      rw [Real.dist_eq,abs_of_nonneg (sub_nonneg.mpr hbx.le)]
      linarith [hx.2]
    · exact mem_cthickening_of_dist_le x x δ (Icc a b)
        ⟨le_of_not_gt hxa,le_of_not_gt hbx⟩ (by simpa using hδ.le)

theorem compact_axis_rectangle {a b : ℝ} (hab : a ≤ b) {U : Set Base}
    (hU : IsOpen U) (haxis : ∀ t ∈ Icc a b, (![0,t] : Base) ∈ U) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ Icc (-δ) δ, ∀ t ∈ Icc (a-δ) (b+δ),
      (![x,t] : Base) ∈ U := by
  let T : ℝ × ℝ → Base := fun z => ![z.1,z.2]
  have hT : Continuous T := by
    apply continuous_pi
    intro i
    fin_cases i
    · exact continuous_fst
    · exact continuous_snd
  have hTU : ({0} : Set ℝ) ×ˢ Icc a b ⊆ T ⁻¹' U := by
    rintro ⟨x,t⟩ ⟨hx,ht⟩
    obtain rfl : x = 0 := hx
    exact haxis t ht
  obtain ⟨V,W,hV,hW,h0V,hIW,hVW⟩ :=
    generalized_tube_lemma isCompact_singleton isCompact_Icc (hU.preimage hT) hTU
  obtain ⟨r,hr,hrV⟩ := Metric.isOpen_iff.mp hV 0 (h0V (by simp))
  obtain ⟨η,hη,hηW⟩ := open_interval_collar hab hW hIW
  let δ := min (r/2) η
  have hδ : 0 < δ := lt_min (half_pos hr) hη
  refine ⟨δ,hδ,?_⟩
  intro x hx t ht
  change (x,t) ∈ T ⁻¹' U
  apply hVW
  constructor
  · apply hrV
    rw [Metric.mem_ball,Real.dist_eq,sub_zero,abs_lt]
    have hδr : δ < r := (min_le_left _ _).trans_lt (half_lt_self hr)
    constructor <;> linarith [hx.1,hx.2]
  · apply hηW
    have hδη : δ ≤ η := min_le_right _ _
    constructor <;> linarith [ht.1,ht.2]

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
