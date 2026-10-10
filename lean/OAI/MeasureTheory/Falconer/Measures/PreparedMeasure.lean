import OAI.MeasureTheory.Falconer.Estimates.PreparedPair
import OAI.MeasureTheory.Falconer.Estimates.PrunedVariation

namespace OAI

/-! # The fixed positive weighted source of the shell reconstruction

All weights and distances use the original ambient space.
The coarse filters may vary with scale; the source measure does not.
-/
namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {d : ℕ} {E : Set (Space d)} {ε : ℝ}

namespace PreparedOriginalPair

noncomputable def source (p : PreparedOriginalPair E ε) : Measure (Space d × Space d) :=
  ((p.pair.left : Measure (Space d)).prod (p.pair.right : Measure (Space d))).withDensity
    (distanceWeight (((d:ℝ)-1)/2))

theorem weight_bounds (p : PreparedOriginalPair E ε) (hd : 1 ≤ d) :
    ∀ᵐ z ∂((p.pair.left : Measure (Space d)).prod (p.pair.right : Measure (Space d))),
      ENNReal.ofReal ((2*p.pair.radius)^(-(((d:ℝ)-1)/2))) ≤
        distanceWeight (((d:ℝ)-1)/2) z ∧
      distanceWeight (((d:ℝ)-1)/2) z ≤
        ENNReal.ofReal ((p.pair.radius/2)^(-(((d:ℝ)-1)/2))) := by
  have hmem := (mem_ae_iff_prob_eq_one p.pair.relation_measurable).mpr p.pair.relation_mass
  have ha : 0 ≤ ((d:ℝ)-1)/2 := by
    have hd' : (1:ℝ) ≤ d := by exact_mod_cast hd
    linarith
  filter_upwards [hmem] with z hz
  obtain ⟨hlo,hhi,_⟩ := p.pair.geometry z.1 hz.1 z.2 hz.2
  have hr : 0 < p.pair.radius/2 := half_pos p.pair.radius_pos
  constructor <;> apply ENNReal.ofReal_le_ofReal
  · exact Real.rpow_le_rpow_of_nonpos (hr.trans_le hlo) hhi (neg_nonpos.mpr ha)
  · exact Real.rpow_le_rpow_of_nonpos hr hlo (neg_nonpos.mpr ha)

theorem source_finite (p : PreparedOriginalPair E ε) (hd : 1 ≤ d) :
    IsFiniteMeasure p.source :=
  finite_withDensity_of_bounded _ _ ENNReal.ofReal_lt_top ((p.weight_bounds hd).mono fun _ h => h.2)

theorem source_positive (p : PreparedOriginalPair E ε) (hd : 1 ≤ d)
    (S : Set (Space d × Space d)) (hS : MeasurableSet S)
    (hpos : 0 < ((p.pair.left : Measure (Space d)).prod (p.pair.right : Measure (Space d))) S) :
    0 < p.source S := by
  apply withDensity_positive_of_lower _ _ _ ((p.weight_bounds hd).mono fun _ h => h.1) S hS hpos
  exact ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos (by linarith [p.pair.radius_pos]) _)

theorem source_carried (p : PreparedOriginalPair E ε) :
    p.source ((fun z : Space d × Space d => dist z.1 z.2) ⁻¹' (distanceSet E)ᶜ) = 0 := by
  apply withDensity_absolutelyContinuous _ _
  have hleft : (p.pair.left : Measure (Space d)) Eᶜ = 0 := by
    apply measure_mono_null _ Measure.measure_compl_support
    exact compl_subset_compl.mpr p.left_subset
  have hright : (p.pair.right : Measure (Space d)) Eᶜ = 0 := by
    apply measure_mono_null _ Measure.measure_compl_support
    exact compl_subset_compl.mpr p.right_subset
  apply measure_mono_null _ (product_carried _ _ E hleft hright)
  intro z hz hzin
  exact hz ⟨z.1,hzin.1,z.2,hzin.2,rfl⟩

end PreparedOriginalPair
end Falconer

end OAI
