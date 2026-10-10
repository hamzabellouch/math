import OAI.Analysis.FiniteFactor.CrossedProduct.TagLaw
import OAI.Analysis.FiniteFactor.Coupling.CoordinateMass

namespace OAI

namespace FiniteFactor
open MeasureTheory
open scoped ENNReal
noncomputable section
namespace CouplingParameters

def currentBoundary (p : CouplingParameters) : Set (Fin 6 × (ℝ × ℝ)) :=
  {z | z.2.1 < 1-2/p.m ∧ 2/p.m < z.2.2}

def currentTag (p : CouplingParameters) : Set (Fin 6 × (ℝ × ℝ)) :=
  {z | z.1 = 5} ∩ p.currentBoundary

def currentNonTag (p : CouplingParameters) : Set (Fin 6 × (ℝ × ℝ)) :=
  {z | z.1 ≠ 5} ∩ p.currentBoundary

theorem currentBoundary_measurable (p : CouplingParameters) : MeasurableSet p.currentBoundary :=
  (measurableSet_lt (measurable_fst.comp measurable_snd) measurable_const).inter
  (measurableSet_lt measurable_const (measurable_snd.comp measurable_snd))

theorem currentTag_measurable (p : CouplingParameters) : MeasurableSet p.currentTag :=
  ((measurableSet_singleton (5 : Fin 6)).preimage measurable_fst).inter p.currentBoundary_measurable

theorem currentNonTag_measurable (p : CouplingParameters) : MeasurableSet p.currentNonTag :=
  (((measurableSet_singleton (5 : Fin 6)).preimage measurable_fst).compl).inter p.currentBoundary_measurable

theorem currentTag_mass (p : CouplingParameters) :
    p.labelledCoupling p.currentTag = ENNReal.ofReal p.tagMass := by
  have hsmall : 1/p.m + 2/p.m < 1 := by
    rw [← add_div]
    apply (div_lt_one p.m_pos).mpr
    linarith [p.m_ge]
  have he : p.currentTag =ᵐ[p.labelledCoupling] {z | z.1 = 5} := by
    filter_upwards [p.labelledCoupling_tag_support] with z hz
    apply propext
    constructor
    · exact fun h => h.1
    · intro h
      obtain ⟨hx,hy⟩ := hz h
      exact ⟨h,by constructor <;> linarith⟩
  rw [measure_congr he,p.labelledCoupling_label]
  rfl

theorem currentTag_disjoint (p : CouplingParameters) : Disjoint p.currentTag p.currentNonTag := by
  apply Set.disjoint_left.mpr
  intro z ht ha
  exact ha.1 ht.1

/-- The source's one-coordinate nontagged admissible mass, including both
endpoint losses, under the actual labelled coupling. -/
theorem currentNonTag_mass_lower (p : CouplingParameters) :
    ENNReal.ofReal (1-41/p.m) ≤ p.labelledCoupling p.currentNonTag := by
  let L : Set (Fin 6 × (ℝ × ℝ)) := {z | z.1 = 5}
  let X : Set (Fin 6 × (ℝ × ℝ)) := {z | 1-2/p.m ≤ z.2.1}
  let Y : Set (Fin 6 × (ℝ × ℝ)) := {z | z.2.2 ≤ 2/p.m}
  have he : p.currentNonTagᶜ = (L ∪ X) ∪ Y := by
    ext z
    simp only [currentNonTag,currentBoundary,L,X,Y,Set.mem_compl_iff,Set.mem_inter_iff,
      Set.mem_union,Set.mem_ofPred_eq,not_and_or,not_not,not_lt]
    tauto
  have hL : p.labelledCoupling.real L ≤ 1/p.m := by
    rw [measureReal_def,p.labelledCoupling_label]
    change (ENNReal.ofReal p.tagMass).toReal ≤ 1/p.m
    rw [ENNReal.toReal_ofReal p.tagMass_nonneg]
    unfold tagMass
    split_ifs
    · exact le_rfl
    · exact div_nonneg zero_le_one p.m_pos.le
  have hX : p.labelledCoupling.real X ≤ 10*(2/p.m) :=
    ENNReal.toReal_le_of_le_ofReal (mul_nonneg (by norm_num) (div_nonneg (by norm_num) p.m_pos.le)) (p.labelledCoupling_right_tail (2/p.m))
  have hY : p.labelledCoupling.real Y ≤ 10*(2/p.m) :=
    ENNReal.toReal_le_of_le_ofReal (mul_nonneg (by norm_num) (div_nonneg (by norm_num) p.m_pos.le)) (p.labelledCoupling_left_tail (2/p.m))
  have hc := (measureReal_union_le (μ := p.labelledCoupling) (L ∪ X) Y).trans
    (add_le_add (measureReal_union_le (μ := p.labelledCoupling) L X) le_rfl)
  rw [← he,measureReal_compl p.currentNonTag_measurable] at hc
  simp only [probReal_univ] at hc
  have hh : 1-41/p.m ≤ p.labelledCoupling.real p.currentNonTag := by
    have hid : 41/p.m = 1/p.m + 10*(2/p.m) + 10*(2/p.m) := by ring
    rw [hid]
    linarith
  exact (ENNReal.ofReal_le_ofReal hh).trans_eq (ENNReal.ofReal_toReal (measure_ne_top _ _))

end CouplingParameters
end
end FiniteFactor

end OAI
