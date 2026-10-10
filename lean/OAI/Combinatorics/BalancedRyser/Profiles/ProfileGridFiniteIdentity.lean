import OAI.Combinatorics.BalancedRyser.Profiles.ProfileFiniteMarks
import OAI.Combinatorics.BalancedRyser.Profiles.ProfileGridCounting
import OAI.Combinatorics.BalancedRyser.Profiles.ProfileGridDetection

namespace OAI

noncomputable section
open MeasureTheory
open scoped BigOperators Classical
namespace Balanced.ProfileGridDetection
open ProfileFiniteMarks ProfileScheduledMarks ProfileDetectionBridge

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

theorem grid_empirical_eq_expect (D C E : Finset (Line F))
    (s : ℕ → Set Profile) (hs : ∀ i, MeasurableSet (s i)) :
    (∑ i ∈ Finset.range E.card,
      (empiricalProfileMeasure D C E : Measure Profile).real (s i)) / E.card =
    (∑ i : Fin E.card, 𝔼 x : E,
      if lineProfile D C x ∈ s i.val then (1 : ℝ) else 0) / Fintype.card F := by
  have hsection i : (empiricalProfileMeasure D C E : Measure Profile).real (s i) =
      (Fintype.card F : ℝ)⁻¹ * ∑ x : E,
        if lineProfile D C x ∈ s i then (1 : ℝ) else 0 := by
    rw [FiniteProfile.empiricalProfileMeasure_real_apply D C E (s i) (hs i)]
    rw [Finset.sum_coe_sort E (fun x => if lineProfile D C x ∈ s i then (1 : ℝ) else 0)]
  simp_rw [hsection, Finset.expect_eq_sum_div_card, Finset.card_univ,
    Fintype.card_coe]
  rw [← Finset.mul_sum, ← Finset.sum_div]
  rw [Fin.sum_univ_eq_sum_range (fun i : ℕ => ∑ x : E,
    if lineProfile D C x ∈ s i then (1 : ℝ) else 0)]
  simp only [div_eq_mul_inv]
  ring

theorem dGridCutoffMass_eq_dFinite (D C : Finset (Line F)) (t : ℕ) :
    dGridCutoffMass D C t = dFinite D C (1 / ((t : ℝ) + 1))
      (1 / ((t : ℝ) + 1)) := by
  unfold dGridCutoffMass
  rw [grid_empirical_eq_expect D C D _ (fun i => by
    have hm := (ProfileDetectionLimit.measurable_dDiscrepancy (planeProfile D C)).comp
      (measurable_id.prodMk (measurable_const (a := (((i + 1 : ℕ) : ℝ) / D.card))))
    simp only [ProfileDetection.cutoffDetection, Set.mem_ofPred_eq]
    refine MeasurableSet.inter ?_ (MeasurableSet.inter ?_ ?_)
    · exact measurableSet_lt (measurable_const (a := (1 / ((t : ℝ) + 1))))
        (measurable_const (a := (((i + 1 : ℕ) : ℝ) / D.card)))
    · exact measurableSet_lt (measurable_const (a := (((i + 1 : ℕ) : ℝ) / D.card)))
        (measurable_const (a := (1 : ℝ)))
    · exact measurableSet_lt measurable_const hm.abs)]
  unfold dFinite detectionSum
  rw [sum_zD D (fun z => 𝔼 x : D,
    if 1 / ((t : ℝ) + 1) < z ∧ z < 1 ∧
      3 * (1 / ((t : ℝ) + 1)) < |dTest (lineProfile D C x) z -
        planeTest (planeProfile D C) z| then (1 : ℝ) else 0)]
  simp only [ProfileDetection.cutoffDetection, Set.mem_ofPred_eq,
    ProfileDetectionLimit.dDiscrepancy, ExposureInterleaving.grid,
    Nat.cast_add, Nat.cast_one, mul_one_div]

theorem cGridCutoffMass_eq_cFinite (D C : Finset (Line F)) (t : ℕ) :
    cGridCutoffMass D C t = cFinite D C (1 / ((t : ℝ) + 1))
      (1 / ((t : ℝ) + 1)) := by
  unfold cGridCutoffMass
  rw [grid_empirical_eq_expect D C C _ (fun i => by
    have hm := (ProfileDetectionLimit.measurable_cDiscrepancy (planeProfile D C)).comp
      (measurable_id.prodMk (measurable_const (a := ((((i + 1 : ℕ) : ℝ) / C.card) ^ (Real.sqrt 2)⁻¹))))
    simp only [ProfileDetection.cutoffDetection, Set.mem_ofPred_eq]
    refine MeasurableSet.inter ?_ (MeasurableSet.inter ?_ ?_)
    · exact measurableSet_lt (measurable_const (a := (1 / ((t : ℝ) + 1))))
        (measurable_const (a := ((((i + 1 : ℕ) : ℝ) / C.card) ^ (Real.sqrt 2)⁻¹)))
    · exact measurableSet_lt (measurable_const (a := ((((i + 1 : ℕ) : ℝ) / C.card) ^ (Real.sqrt 2)⁻¹)))
        (measurable_const (a := (1 : ℝ)))
    · exact measurableSet_lt measurable_const hm.abs)]
  unfold cFinite detectionSum
  rw [sum_zC C (fun z => 𝔼 x : C,
    if 1 / ((t : ℝ) + 1) < z ∧ z < 1 ∧
      3 * (1 / ((t : ℝ) + 1)) < |cTest (lineProfile D C x) z -
        planeTest (planeProfile D C) z| then (1 : ℝ) else 0)]
  simp only [ProfileDetection.cutoffDetection, Set.mem_ofPred_eq,
    ProfileDetectionLimit.cDiscrepancy, ExposureInterleaving.coverGrid,
    ExposureInterleaving.grid, Nat.cast_add, Nat.cast_one, mul_one_div]

end Balanced.ProfileGridDetection

end

end OAI
