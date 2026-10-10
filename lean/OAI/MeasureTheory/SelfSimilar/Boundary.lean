import OAI.MeasureTheory.SelfSimilar.RandomGrid

namespace OAI

universe uα

section
open scoped BigOperators ENNReal
open MeasureTheory
namespace EntropyRateDimension
namespace Boundary
open Set

noncomputable def increment (a u : ℝ) : ℝ := (⌊u+a⌋ : ℝ)-(⌊u⌋ : ℝ)

theorem increment_periodic (a : ℝ) : Function.Periodic (increment a) 1 := by
  intro u
  simp only [increment,add_right_comm u 1 a, Int.floor_add_one, Int.cast_add, Int.cast_one]
  ring

theorem increment_bounds {a : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1) (u : ℝ) :
    0 ≤ increment a u ∧ increment a u ≤ 1 := by
  have hl := Int.floor_le_floor (show u ≤ u+a by linarith)
  have hu := Int.floor_le_floor (show u+a ≤ u+1 by linarith)
  rw [Int.floor_add_one] at hu
  have hl' : (⌊u⌋ : ℝ) ≤ (⌊u+a⌋ : ℝ) := by exact_mod_cast hl
  have hu' : (⌊u+a⌋ : ℝ) ≤ (⌊u⌋ : ℝ)+1 := by exact_mod_cast hu
  unfold increment
  constructor <;> linarith

theorem increment_measurable (a : ℝ) : Measurable (increment a) := by
  unfold increment
  exact (((measurable_of_countable (fun n : ℤ => (n : ℝ))).comp
    (measurable_id.add_const a).floor)).sub
    ((measurable_of_countable (fun n : ℤ => (n : ℝ))).comp measurable_id.floor)

theorem increment_integrable {a : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1) (b c : ℝ) :
    IntervalIntegrable (increment a) volume b c := by
  apply (intervalIntegrable_const (c := (1 : ℝ))).mono_fun'
    (increment_measurable a).aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun u => by
    change ‖increment a u‖ ≤ (1 : ℝ)
    rw [Real.norm_eq_abs,abs_of_nonneg (increment_bounds ha ha1 u).1]
    exact (increment_bounds ha ha1 u).2)

theorem increment_eq_indicator {a u : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1)
    (hu : u ∈ Ioo (0 : ℝ) 1) :
    increment a u = (Icc (1-a) 1).indicator (fun _ => (1 : ℝ)) u := by
  have hfl : ⌊u⌋=(0 : ℤ) := Int.floor_eq_zero_iff.mpr ⟨hu.1.le,hu.2⟩
  by_cases h : 1-a ≤ u
  · have hf : ⌊u+a⌋=(1 : ℤ) := Int.floor_eq_iff.mpr (by
      norm_num
      constructor <;> linarith [hu.2])
    simp [increment,hfl,hf,Set.indicator_of_mem (show u ∈ Icc (1-a) 1 from ⟨h,hu.2.le⟩)]
  · have hf : ⌊u+a⌋=(0 : ℤ) := Int.floor_eq_zero_iff.mpr (by constructor <;> linarith [hu.1])
    simp [increment,hfl,hf,Set.indicator_of_notMem (show u ∉ Icc (1-a) 1 from fun hh => h hh.1)]

theorem integral_increment {a : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1) :
    (∫ u in (0 : ℝ)..1, increment a u) = a := by
  rw [intervalIntegral.integral_of_le zero_le_one,integral_Ioc_eq_integral_Ioo]
  have he := setIntegral_congr_fun (μ := (volume : Measure ℝ)) measurableSet_Ioo (fun u hu => increment_eq_indicator ha ha1 hu)
  rw [he,integral_indicator measurableSet_Icc,Measure.restrict_restrict measurableSet_Icc]
  have hi : (Ioo (0 : ℝ) 1 : Set ℝ) =ᵐ[volume] (Icc 0 1 : Set ℝ) := Ioo_ae_eq_Icc
  have hs : (Icc (1-a) 1 ∩ Ioo (0 : ℝ) 1 : Set ℝ) =ᵐ[volume] (Icc (1-a) 1 : Set ℝ) := by
    filter_upwards [hi] with u hu
    change (u ∈ Ioo (0 : ℝ) 1) = (u ∈ Icc 0 1) at hu
    apply propext
    constructor
    · exact fun h => h.1
    · intro h
      exact ⟨h,hu.mpr ⟨by linarith [h.1],h.2⟩⟩

  rw [Measure.restrict_congr_set hs,integral_const]
  simp only [Measure.real,Measure.restrict_apply_univ,Real.volume_Icc,smul_eq_mul,mul_one]
  rw [ENNReal.toReal_ofReal (by linarith : 0 ≤ 1-(1-a))]
  ring

theorem integral_increment_shift {a : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1) (b : ℝ) :
    (∫ u in (0 : ℝ)..1, increment a (u+b)) = a := by
  rw [intervalIntegral.integral_comp_add_right]
  have h := (increment_periodic a).intervalIntegral_add_eq b 0
  simpa only [zero_add,add_comm 1 b,integral_increment ha ha1] using h

theorem increment_eq_ite {a : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1) (u : ℝ) :
    increment a u = if ⌊u+a⌋=⌊u⌋ then 0 else 1 := by
  classical
  have hl := Int.floor_le_floor (show u ≤ u+a by linarith)
  have hu := Int.floor_le_floor (show u+a ≤ u+1 by linarith)
  rw [Int.floor_add_one] at hu
  by_cases h : ⌊u+a⌋=⌊u⌋
  · simp [increment,h]
  · have he : ⌊u+a⌋=⌊u⌋+1 := by omega
    simp [increment,he]

theorem increment_prod_integrable {α : Type uα} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] {a : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1)
    (b : α → ℝ) (hb : Measurable b) :
    Integrable (fun ux : ℝ × α => increment a (ux.1+b ux.2))
      ((volume.restrict (Ioc (0 : ℝ) 1)).prod μ) := by
  let : IsProbabilityMeasure (volume.restrict (Ioc (0 : ℝ) 1)) := ⟨by simp⟩
  apply (integrable_const (1 : ℝ)).mono'
    ((increment_measurable a).comp (measurable_fst.add (hb.comp measurable_snd))).aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun ux => by
    change ‖increment a (ux.1+b ux.2)‖ ≤ (1 : ℝ)
    rw [Real.norm_eq_abs,abs_of_nonneg (increment_bounds ha ha1 _).1]
    exact (increment_bounds ha ha1 _).2)

theorem increment_measure_intervalIntegrable {α : Type uα} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] {a : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1)
    (b : α → ℝ) (hb : Measurable b) :
    IntervalIntegrable (fun u => ∫ x, increment a (u+b x) ∂μ) volume 0 1 := by
  apply (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mpr
  exact (increment_prod_integrable μ ha ha1 b hb).integral_prod_left

theorem integral_increment_measure {α : Type uα} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] {a : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1)
    (b : α → ℝ) (hb : Measurable b) :
    (∫ u in (0 : ℝ)..1, ∫ x, increment a (u+b x) ∂μ) = a := by
  have hp := increment_prod_integrable μ ha ha1 b hb
  have hs : Integrable (Function.uncurry (fun u x => increment a (u+b x)))
      ((volume.restrict (uIoc (0 : ℝ) 1)).prod μ) := by
    rw [uIoc_of_le zero_le_one]
    convert hp using 1
    rfl
  rw [intervalIntegral_integral_swap hs]
  simp only [integral_increment_shift ha ha1,integral_const,probReal_univ,one_smul]

end Boundary

end EntropyRateDimension
end

end OAI
