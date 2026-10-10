import OAI.Analysis.CircleDomains.Sobolev.TensorAverageBound

namespace OAI

/-! Fubini for finite-measure averages and an integrated row estimate. -/
open Set Function Filter MeasureTheory
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

lemma product_average {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {μ : Measure X} {ν : Measure Y} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {f : X × Y → ℝ} (hf : Integrable f (μ.prod ν)) :
    (⨍ p, f p ∂μ.prod ν) = ⨍ x, ⨍ y, f (x,y) ∂ν ∂μ := by
  have hm : (μ.prod ν).real univ = μ.real univ * ν.real univ := by
    simpa only [univ_prod_univ] using (measureReal_prod_prod (μ := μ) (ν := ν) univ univ)
  simp only [average_eq, smul_eq_mul, hm, integral_const_mul, integral_prod _ hf, mul_inv_rev]
  ring

lemma iterated_average_swap {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {μ : Measure X} {ν : Measure Y} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {f : X × Y → ℝ} (hf : Integrable f (μ.prod ν)) :
    (⨍ x, ⨍ y, f (x,y) ∂ν ∂μ) = ⨍ y, ⨍ x, f (x,y) ∂μ ∂ν := by
  simp only [average_eq, smul_eq_mul, integral_const_mul]
  rw [integral_integral_swap (f := fun x y => f (x,y)) hf]
  ring

lemma average_integral_first {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {μ : Measure X} {ν : Measure Y} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {f : X × Y → ℝ} (hf : Integrable f (μ.prod ν)) :
    (⨍ y, ∫ x, f (x,y) ∂μ ∂ν) = μ.real univ * (⨍ p, f p ∂μ.prod ν) := by
  simp_rw [← measure_smul_average μ (fun x => f (x,_)), smul_eq_mul]
  rw [average_const_mul, ← iterated_average_swap hf, ← product_average hf]

lemma average_integral_second {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {μ : Measure X} {ν : Measure Y} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {f : X × Y → ℝ} (hf : Integrable f (μ.prod ν)) :
    (⨍ x, ∫ y, f (x,y) ∂ν ∂μ) = ν.real univ * (⨍ p, f p ∂μ.prod ν) := by
  simp_rw [← measure_smul_average ν (fun y => f (_,y)), smul_eq_mul]
  rw [average_const_mul, ← product_average hf]

lemma iterated_average_row_bound {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {μ : Measure X} {ν : Measure Y} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    [NeZero μ] [NeZero ν] {f : X × Y → ℝ} {H : Y → ℝ} {C : ℝ}
    (hf : Integrable f (μ.prod ν)) (hH : Integrable H ν)
    (h : ∀ᵐ y ∂ν, ∀ᵐ x ∂μ, f (x,y) ≤ H y+C) :
    (⨍ y, ⨍ x, f (x,y) ∂μ ∂ν) ≤ (⨍ y, H y ∂ν)+C := by
  have hi : Integrable (fun y => ⨍ x, f (x,y) ∂μ) ν := by
    simp only [average_eq, smul_eq_mul]
    exact hf.integral_prod_right.const_mul _
  have hh : (fun y => ⨍ x, f (x,y) ∂μ) ≤ᵐ[ν] fun y => H y+C := by
    filter_upwards [hf.prod_left_ae, h] with y hy hle
    simpa only [average_const] using average_mono_real hy (integrable_const (H y+C)) hle
  have he : (⨍ y, H y+C ∂ν) = (⨍ y, H y ∂ν)+C := by
    simpa only [Pi.add_apply, average_const] using average_add hH (integrable_const C)
  exact (average_mono_real hi (hH.add (integrable_const C)) hh).trans_eq he

end CircleDomainRigidity

end

end OAI
