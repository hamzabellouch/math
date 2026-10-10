import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.MeasureTheory.Measure.Hausdorff
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Topology.Instances.AddCircle.Defs
import Mathlib.GroupTheory.QuotientGroup.ModEq

namespace OAI

/-!
# Periodizing scalar coarea lengths

A scalar coarea estimate controls the integral of the physical length
of real level sets. Integer translates of `[0,1)` partition the real
line, so the sum of these lengths over all lifts of a mod-one level
has the same integral on `[0,1)`. Countable subadditivity then gives
finite physical length for almost every mod-one level.
-/

open Set MeasureTheory Metric Function
open scoped ENNReal

namespace CircleDomainRigidity

/-- Equality modulo one is equality up to an integer translation. -/
theorem unitAddCircle_eq_iff_exists_int {a b : ℝ} :
    (a : UnitAddCircle) = (b : UnitAddCircle) ↔ ∃ k : ℤ, a = b + (k : ℝ) := by
  rw [← AddCommGroup.modEq_iff_eq_mod_zmultiples, AddCommGroup.modEq_comm,
    AddCommGroup.modEq_iff_eq_add_zsmul]
  simp only [zsmul_eq_mul, mul_one]

/-- The actual mod-one fiber of any real coordinate is the countable
union of its integer-translated scalar fibers. -/
theorem unitAddCircle_level_eq_iUnion_integer_levels {Z : Type*} (f : Z → ℝ) (t : ℝ) :
    {x | (f x : UnitAddCircle) = (t : UnitAddCircle)} =
      ⋃ k : ℤ, {x | f x = t + (k : ℝ)} := by
  ext x
  simp only [mem_ofPred_eq, mem_iUnion, unitAddCircle_eq_iff_exists_int]

theorem unitAddCircle_level_inter_eq_iUnion_integer_levels
    {Z : Type*} (f : Z → ℝ) (D : Set Z) (t : ℝ) :
    D ∩ {x | (f x : UnitAddCircle) = (t : UnitAddCircle)} =
      ⋃ k : ℤ, D ∩ {x | f x = t + (k : ℝ)} := by
  rw [unitAddCircle_level_eq_iUnion_integer_levels, inter_iUnion]

noncomputable def periodizedLevelLength (L : ℝ → ℝ≥0∞) (t : ℝ) : ℝ≥0∞ :=
  ∑' k : ℤ, L (t + (k : ℝ))

private theorem iUnion_integer_Ico : (⋃ k : ℤ, Ico (k : ℝ) ((k : ℝ) + 1)) = univ := by
  apply Set.eq_univ_of_forall
  intro x
  exact mem_iUnion.mpr ⟨⌊x⌋, Int.floor_le x, Int.lt_floor_add_one x⟩

private theorem pairwise_disjoint_integer_Ico :
    Pairwise (Disjoint on fun k : ℤ => Ico (k : ℝ) ((k : ℝ) + 1)) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  rintro x ⟨hxi, hxi'⟩ ⟨hxj, hxj'⟩
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · have hstep : i + 1 ≤ j := by omega
    have hcast : (i : ℝ) + 1 ≤ (j : ℝ) := by exact_mod_cast hstep
    linarith
  · have hstep : j + 1 ≤ i := by omega
    have hcast : (j : ℝ) + 1 ≤ (i : ℝ) := by exact_mod_cast hstep
    linarith

theorem measurable_periodizedLevelLength (L : ℝ → ℝ≥0∞) (hL : Measurable L) :
    Measurable (periodizedLevelLength L) :=
  Measurable.tsum (fun k : ℤ => hL.comp (measurable_id.add_const (k : ℝ)))

/-- Tonelli and the integer translates of a unit interval give the exact
periodized coarea integral. -/
theorem lintegral_periodizedLevelLength (L : ℝ → ℝ≥0∞) (hL : Measurable L) :
    ∫⁻ t in Ico (0 : ℝ) 1, periodizedLevelLength L t = ∫⁻ t, L t := by
  unfold periodizedLevelLength
  have hm (k : ℤ) : AEMeasurable (fun t : ℝ => L (t + (k : ℝ)))
      (volume.restrict (Ico (0 : ℝ) 1)) :=
    (hL.comp (measurable_id.add_const (k : ℝ))).aemeasurable
  rw [lintegral_tsum hm]
  have hshift (k : ℤ) :
      ∫⁻ t in Ico (0 : ℝ) 1, L (t + (k : ℝ)) =
        ∫⁻ t in Ico (k : ℝ) ((k : ℝ) + 1), L t := by
    have h := (measurePreserving_add_right volume (k : ℝ)).setLIntegral_comp_emb
      (Homeomorph.addRight (k : ℝ)).isClosedEmbedding.measurableEmbedding L (Ico 0 1)
    simpa only [image_add_const_Ico, zero_add, add_comm (1 : ℝ) (k : ℝ)] using h
  simp_rw [hshift]
  rw [← lintegral_iUnion (fun _ : ℤ => measurableSet_Ico) pairwise_disjoint_integer_Ico,
    iUnion_integer_Ico, Measure.restrict_univ]

theorem ae_finite_periodizedLevelLength (L : ℝ → ℝ≥0∞) (hL : Measurable L)
    (hfinite : ∫⁻ t, L t < ∞) :
    ∀ᵐ t ∂volume.restrict (Ico (0 : ℝ) 1), periodizedLevelLength L t < ∞ := by
  apply ae_lt_top (measurable_periodizedLevelLength L hL)
  rw [lintegral_periodizedLevelLength L hL]
  exact hfinite.ne

/-- A mod-one physical level is a union of its scalar lifts. Its
Hausdorff length is bounded by the periodized scalar coarea bound and
is therefore finite almost everywhere on the fundamental interval. -/
theorem ae_finite_hausdorffMeasure_mod_one_levels
    {Z : Type*} [MetricSpace Z] [MeasurableSpace Z] [BorelSpace Z]
    (L : ℝ → ℝ≥0∞) (hL : Measurable L) (hfinite : ∫⁻ t, L t < ∞)
    (A H : ℝ → Set Z)
    (hcover : ∀ t, H t ⊆ ⋃ k : ℤ, A (t + (k : ℝ)))
    (hlength : ∀ r, (μH[1] : Measure Z) (A r) ≤ L r) :
    ∀ᵐ t ∂volume.restrict (Ico (0 : ℝ) 1), (μH[1] : Measure Z) (H t) < ∞ := by
  filter_upwards [ae_finite_periodizedLevelLength L hL hfinite] with t ht
  apply lt_of_le_of_lt _ ht
  calc
    (μH[1] : Measure Z) (H t) ≤ (μH[1] : Measure Z) (⋃ k : ℤ, A (t + (k : ℝ))) :=
      measure_mono (hcover t)
    _ ≤ ∑' k : ℤ, (μH[1] : Measure Z) (A (t + (k : ℝ))) := measure_iUnion_le _
    _ ≤ periodizedLevelLength L t := ENNReal.tsum_le_tsum (fun k => hlength (t + (k : ℝ)))

/-- Applying the periodization argument to actual scalar and circle
fibers removes the countable-union premise. The real-level estimate is
exactly the specialization supplied by scalar coarea. -/
theorem ae_finite_hausdorffMeasure_scalar_mod_one_levels
    {Z : Type*} [MetricSpace Z] [MeasurableSpace Z] [BorelSpace Z]
    (f : Z → ℝ) (D : Set Z) (L : ℝ → ℝ≥0∞) (hL : Measurable L)
    (hfinite : ∫⁻ t, L t < ∞)
    (hlength : ∀ r, (μH[1] : Measure Z) (D ∩ {x | f x = r}) ≤ L r) :
    ∀ᵐ (t : ℝ) ∂volume.restrict (Ico (0 : ℝ) 1),
      (μH[1] : Measure Z) (D ∩ {x | (f x : UnitAddCircle) = (t : UnitAddCircle)}) < ∞ := by
  apply ae_finite_hausdorffMeasure_mod_one_levels L hL hfinite
    (fun r => D ∩ {x | f x = r})
    (fun t => D ∩ {x | (f x : UnitAddCircle) = (t : UnitAddCircle)})
  · intro t
    rw [unitAddCircle_level_inter_eq_iUnion_integer_levels]
  · exact hlength

end CircleDomainRigidity

end OAI
