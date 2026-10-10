import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.Tactic

namespace OAI

open MeasureTheory Set
open scoped BigOperators

namespace Invariant233.DigitAveraging

theorem sq_integral_le_mass_mul_integral_sq
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {u : Ω → ℝ} (hu : Integrable u μ)
    (hu2 : Integrable (fun x => u x ^ 2) μ) (hM : 0 < μ.real univ) :
    (∫ x, u x ∂μ) ^ 2 ≤ μ.real univ * ∫ x, u x ^ 2 ∂μ := by
  let M := μ.real univ
  let A := ∫ x, u x ∂μ
  let a := A / M
  have ha : a * M = A := div_mul_cancel₀ A (ne_of_gt hM)
  have he : (∫ x, (u x - a) ^ 2 ∂μ) =
      (∫ x, u x ^ 2 ∂μ) - 2 * a * A + a ^ 2 * M := by
    have hlin : Integrable (fun x => 2 * a * u x) μ := hu.const_mul _
    have hconst : Integrable (fun _ : Ω => a ^ 2) μ := integrable_const _
    have hpoint : (fun x => (u x - a) ^ 2) =
        (fun x => u x ^ 2 - 2 * a * u x + a ^ 2) := by
      funext x
      ring
    rw [hpoint, integral_add (show Integrable (fun x => u x ^ 2 - 2 * a * u x) μ from hu2.sub hlin) hconst, integral_sub hu2 hlin,
      integral_const_mul, integral_const]
    simp only [smul_eq_mul, Measure.real, M, A]
    ring
  have hnonneg : 0 ≤ ∫ x, (u x - a) ^ 2 ∂μ := integral_nonneg (fun _ => sq_nonneg _)
  rw [he, ← ha] at hnonneg
  have hb : a ^ 2 * M ≤ ∫ x, u x ^ 2 ∂μ := by nlinarith
  change A ^ 2 ≤ M * ∫ x, u x ^ 2 ∂μ
  calc
    A ^ 2 = (a * M) ^ 2 := congrArg (fun z : ℝ => z ^ 2) ha.symm
    _ = M * (a ^ 2 * M) := by ring
    _ ≤ M * ∫ x, u x ^ 2 ∂μ := mul_le_mul_of_nonneg_left hb hM.le

theorem sum_integral_fibers {Ω α : Type*} [MeasurableSpace Ω]
    [MeasurableSpace α] [MeasurableSingletonClass α] [Fintype α]
    {μ : Measure Ω} {f : Ω → α} (hf : Measurable f)
    {u : Ω → ℝ} (hu : Integrable u μ) :
    (∑ a : α, ∫ x in {x | f x = a}, u x ∂μ) = ∫ x, u x ∂μ := by
  have hm : ∀ a : α, MeasurableSet {x | f x = a} :=
    fun a => hf (measurableSet_singleton a)
  have hd : Pairwise (fun a b : α => Disjoint {x | f x = a} {x | f x = b}) := by
    intro a b hab
    rw [Set.disjoint_left]
    intro x hxa hxb
    exact hab (hxa.symm.trans hxb)
  have hcover : (⋃ a : α, {x | f x = a}) = univ := by
    ext x
    simp
  rw [← integral_iUnion_fintype hm hd (fun _ => hu.integrableOn), hcover,
    Measure.restrict_univ]

theorem digit_averaging_energy_le
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {q : ℕ} (hq : 0 < q) {f : Ω → Fin q} (hf : Measurable f)
    (hmass : ∀ a : Fin q, μ.real {x | f x = a} = 1 / (q : ℝ))
    {h : Ω → ℝ} (hh : MemLp h 2 μ) :
    (1 / (q : ℝ)) * ∑ a : Fin q,
      ((q : ℝ) * (∫ x in {x | f x = a}, h x ∂μ) - 1) ^ 2 ≤
      ∫ x, (h x - 1) ^ 2 ∂μ := by
  have hqR : 0 < (q : ℝ) := by exact_mod_cast hq
  have hq0 : (q : ℝ) ≠ 0 := ne_of_gt hqR
  have hhInt : Integrable h μ := hh.integrable (by norm_num)
  have hu : MemLp (fun x => h x - 1) 2 μ := hh.sub (memLp_const 1)
  have huInt : Integrable (fun x => h x - 1) μ := hu.integrable (by norm_num)
  have hu2Int := hu.integrable_sq
  have hlocal : ∀ a : Fin q,
      (1 / (q : ℝ)) * ((q : ℝ) * (∫ x in {x | f x = a}, h x ∂μ) - 1) ^ 2 ≤
      ∫ x in {x | f x = a}, (h x - 1) ^ 2 ∂μ := by
    intro a
    have hpos : 0 < (μ.restrict {x | f x = a}).real univ := by
      rw [measureReal_restrict_apply_univ, hmass]
      positivity
    have hcs := sq_integral_le_mass_mul_integral_sq
      huInt.restrict hu2Int.restrict hpos
    rw [measureReal_restrict_apply_univ, hmass] at hcs
    have he : (q : ℝ) * (∫ x in {x | f x = a}, h x ∂μ) - 1 =
        (q : ℝ) * (∫ x in {x | f x = a}, h x - 1 ∂μ) := by
      rw [integral_sub hhInt.restrict (integrable_const 1), setIntegral_const]
      simp only [smul_eq_mul, mul_one, hmass]
      field_simp
    rw [he]
    calc
      (1 / (q : ℝ)) * ((q : ℝ) * (∫ x in {x | f x = a}, h x - 1 ∂μ)) ^ 2 =
          (q : ℝ) * (∫ x in {x | f x = a}, h x - 1 ∂μ) ^ 2 := by field_simp
      _ ≤ (q : ℝ) * ((1 / (q : ℝ)) *
          (∫ x in {x | f x = a}, (h x - 1) ^ 2 ∂μ)) :=
        mul_le_mul_of_nonneg_left hcs hqR.le
      _ = ∫ x in {x | f x = a}, (h x - 1) ^ 2 ∂μ := by field_simp
  rw [Finset.mul_sum]
  exact (Finset.sum_le_sum (fun a _ => hlocal a)).trans_eq
    (sum_integral_fibers hf hu2Int)

theorem digit_average_nonneg
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {q : ℕ} {f : Ω → Fin q} {h : Ω → ℝ}
    (hh : ∀ᵐ x ∂μ, 0 ≤ h x) (a : Fin q) :
    0 ≤ (q : ℝ) * (∫ x in {x | f x = a}, h x ∂μ) :=
  mul_nonneg (Nat.cast_nonneg q) (integral_nonneg_of_ae (ae_restrict_of_ae hh))

theorem digit_average_mean
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {q : ℕ} (hq : 0 < q) {f : Ω → Fin q} (hf : Measurable f)
    {h : Ω → ℝ} (hh : Integrable h μ) :
    (1 / (q : ℝ)) * ∑ a : Fin q,
      (q : ℝ) * (∫ x in {x | f x = a}, h x ∂μ) = ∫ x, h x ∂μ := by
  rw [← Finset.mul_sum, sum_integral_fibers hf hh]
  have hq0 : (q : ℝ) ≠ 0 := by positivity
  field_simp

theorem digit_average_le
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {q : ℕ} (hq : 0 < q) {f : Ω → Fin q}
    (hmass : ∀ a : Fin q, μ.real {x | f x = a} = 1 / (q : ℝ))
    {h : Ω → ℝ} (hh : Integrable h μ) {B : ℝ}
    (hB : ∀ᵐ x ∂μ, h x ≤ B) (a : Fin q) :
    (q : ℝ) * (∫ x in {x | f x = a}, h x ∂μ) ≤ B := by
  have hqR : 0 < (q : ℝ) := by exact_mod_cast hq
  have hq0 : (q : ℝ) ≠ 0 := hqR.ne'
  calc
    (q : ℝ) * (∫ x in {x | f x = a}, h x ∂μ) ≤
        (q : ℝ) * (∫ _x in {x | f x = a}, B ∂μ) :=
      mul_le_mul_of_nonneg_left
        (integral_mono_ae hh.restrict (integrable_const B) (ae_restrict_of_ae hB)) hqR.le
    _ = B := by
      rw [setIntegral_const, smul_eq_mul, hmass]
      field_simp

theorem map_withDensity_eq_digit_density
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {q : ℕ} (hq : 0 < q) {f : Ω → Fin q} (hf : Measurable f)
    (hmass : ∀ a : Fin q, μ.real {x | f x = a} = 1 / (q : ℝ))
    {h : Ω → ℝ} (hh : Integrable h μ) (hnonneg : ∀ᵐ x ∂μ, 0 ≤ h x) :
    (μ.withDensity (fun x => ENNReal.ofReal (h x))).map f =
      (μ.map f).withDensity (fun a => ENNReal.ofReal
        ((q : ℝ) * ∫ x in {x | f x = a}, h x ∂μ)) := by
  have hqR : 0 < (q : ℝ) := by exact_mod_cast hq
  have hq0 : (q : ℝ) ≠ 0 := hqR.ne'
  apply Measure.ext_of_singleton
  intro a
  have hfiber : f ⁻¹' {a} = {x | f x = a} := by ext x; simp
  have hmeas : MeasurableSet {x | f x = a} := hf (measurableSet_singleton a)
  have hmapa : (μ.map f) {a} = ENNReal.ofReal (1 / (q : ℝ)) := by
    rw [Measure.map_apply hf (measurableSet_singleton a), hfiber]
    rw [← ENNReal.ofReal_toReal (measure_ne_top μ {x | f x = a})]
    exact congrArg ENNReal.ofReal (hmass a)
  rw [Measure.map_apply hf (measurableSet_singleton a), hfiber,
    withDensity_apply _ hmeas,
    withDensity_apply _ (measurableSet_singleton a), lintegral_singleton, hmapa,
    ← ofReal_integral_eq_lintegral_ofReal hh.restrict (ae_restrict_of_ae hnonneg)]
  rw [← ENNReal.ofReal_mul (digit_average_nonneg hnonneg a)]
  congr 1
  field_simp

theorem integral_map_eq_uniform_sum
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {q : ℕ} {f : Ω → Fin q} (hf : Measurable f)
    (hmass : ∀ a : Fin q, μ.real {x | f x = a} = 1 / (q : ℝ))
    (g : Fin q → ℝ) :
    (∫ a, g a ∂μ.map f) = (1 / (q : ℝ)) * ∑ a : Fin q, g a := by
  have hg : Integrable g (μ.map f) := by
    exact Integrable.of_finite
  rw [integral_fintype hg, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  have hmap : (μ.map f).real {a} = μ.real {x | f x = a} := by
    unfold Measure.real
    rw [Measure.map_apply hf (measurableSet_singleton a)]
    congr 1
  rw [smul_eq_mul, hmap, hmass]

theorem integral_digit_energy_le
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {q : ℕ} (hq : 0 < q) {f : Ω → Fin q} (hf : Measurable f)
    (hmass : ∀ a : Fin q, μ.real {x | f x = a} = 1 / (q : ℝ))
    {h : Ω → ℝ} (hh : MemLp h 2 μ) :
    (∫ a, ((q : ℝ) * (∫ x in {x | f x = a}, h x ∂μ) - 1) ^ 2 ∂μ.map f) ≤
      ∫ x, (h x - 1) ^ 2 ∂μ := by
  rw [integral_map_eq_uniform_sum hf hmass]
  exact digit_averaging_energy_le hq hf hmass hh

end Invariant233.DigitAveraging

end OAI
