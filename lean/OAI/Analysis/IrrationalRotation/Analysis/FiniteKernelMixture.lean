import OAI.Analysis.IrrationalRotation.Model.FiniteKernelMixture
import Mathlib.Tactic

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

namespace Invariant233.FiniteKernelMixture

variable {I X Y : Type*} [Fintype I] [MeasurableSpace X] [MeasurableSpace Y]

@[simp] theorem weightedKernel_apply (κ : I → Kernel X Y) (w : I → X → ℝ≥0∞)
    (hw : ∀ i, Measurable (w i)) (x : X) :
    weightedKernel κ w hw x = ∑ i, w i x • κ i x := rfl

@[simp] theorem normalizedKernel_apply (κ : I → Kernel X Y) (w : I → X → ℝ≥0∞)
    (hw : ∀ i, Measurable (w i)) (x : X) :
    normalizedKernel κ w hw x = ∑ i, (w i x / ∑ j, w j x) • κ i x := rfl

theorem normalizedKernel_isMarkov (κ : I → Kernel X Y) [∀ i, IsMarkovKernel (κ i)]
    (w : I → X → ℝ≥0∞) (hw : ∀ i, Measurable (w i))
    (h0 : ∀ x, (∑ i, w i x) ≠ 0) (ht : ∀ x, (∑ i, w i x) ≠ ∞) :
    IsMarkovKernel (normalizedKernel κ w hw) := by
  constructor
  intro x
  constructor
  simp only [normalizedKernel_apply, Measure.finsetSum_apply,
    Measure.smul_apply, smul_eq_mul, measure_univ, mul_one]
  simp_rw [div_eq_mul_inv]
  rw [← Finset.sum_mul]
  exact ENNReal.mul_inv_cancel (h0 x) (ht x)

theorem normalizedKernel_disintegration (μ : Measure X) [SFinite μ]
    (κ : I → Kernel X Y) [∀ i, IsMarkovKernel (κ i)]
    (w : I → X → ℝ≥0∞) (hw : ∀ i, Measurable (w i))
    (h0 : ∀ x, (∑ i, w i x) ≠ 0) (ht : ∀ x, (∑ i, w i x) ≠ ∞) :
    (μ.withDensity (fun x => ∑ i, w i x)) ⊗ₘ normalizedKernel κ w hw =
      ∑ i, (μ.withDensity (w i)) ⊗ₘ κ i := by
  let := normalizedKernel_isMarkov κ w hw h0 ht
  have hsum : Measurable (fun x => ∑ i, w i x) :=
    Finset.measurable_sum _ (fun i _ => hw i)
  ext s hs
  rw [Measure.compProd_apply hs,
    lintegral_withDensity_eq_lintegral_mul _ hsum
      (Kernel.measurable_kernel_prodMk_left hs)]
  simp only [normalizedKernel_apply, Measure.finsetSum_apply,
    Measure.smul_apply, smul_eq_mul]
  have heach (i : I) :
      ((μ.withDensity (w i)) ⊗ₘ κ i) s =
        ∫⁻ x, w i x * κ i x (Prod.mk x ⁻¹' s) ∂μ := by
    rw [Measure.compProd_apply hs,
      lintegral_withDensity_eq_lintegral_mul _ (hw i)
        (Kernel.measurable_kernel_prodMk_left hs)]
    rfl
  simp_rw [heach]
  calc
    _ = ∫⁻ x, ∑ i, w i x * κ i x (Prod.mk x ⁻¹' s) ∂μ := by
      apply lintegral_congr
      intro x
      change (∑ i, w i x) * (∑ i, (w i x / ∑ j, w j x) * κ i x (Prod.mk x ⁻¹' s)) = _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [← mul_assoc, ENNReal.mul_div_cancel (h0 x) (ht x)]
    _ = _ := lintegral_finsetSum _ (fun i _ =>
      (hw i).mul (Kernel.measurable_kernel_prodMk_left hs))

theorem diagonalReplacementKernel_apply (q : ℝ≥0∞) (p : I → ℝ≥0∞)
    (u : I → X → ℝ≥0∞) (hu : ∀ i, Measurable (u i))
    (ν : I → Measure X) (x : X) :
    diagonalReplacementKernel q p u hu ν x =
      (q / (q + ∑ i, p i * u i x)) • Measure.dirac x +
        ∑ i, (p i * u i x / (q + ∑ j, p j * u j x)) • ν i := by
  simp only [diagonalReplacementKernel, normalizedKernel_apply,
    Fintype.sum_option, Kernel.id_apply, Kernel.const_apply]

theorem diagonalReplacementKernel_isMarkov (q : ℝ≥0∞) (hq : q ≠ 0)
    (p : I → ℝ≥0∞) (u : I → X → ℝ≥0∞) (hu : ∀ i, Measurable (u i))
    (ν : I → Measure X) [∀ i, IsProbabilityMeasure (ν i)]
    (ht : ∀ x, (q + ∑ i, p i * u i x) ≠ ∞) :
    IsMarkovKernel (diagonalReplacementKernel q p u hu ν) := by
  let κ : Option I → Kernel X X := fun o => match o with
    | none => Kernel.id
    | some i => Kernel.const X (ν i)
  have : ∀ o, IsMarkovKernel (κ o) := by
    intro o
    cases o <;> dsimp [κ] <;> infer_instance
  apply normalizedKernel_isMarkov (κ := κ)
  · intro x h
    have h' : q + ∑ i, p i * u i x = 0 := by
      simpa only [Fintype.sum_option] using h
    exact hq (add_eq_zero.mp h').1
  · intro x
    simpa only [Fintype.sum_option] using ht x

theorem diagonalReplacementKernel_disintegration (μ : Measure X) [SFinite μ]
    (q : ℝ≥0∞) (hq : q ≠ 0) (p : I → ℝ≥0∞)
    (u : I → X → ℝ≥0∞) (hu : ∀ i, Measurable (u i))
    (ν : I → Measure X) [∀ i, IsProbabilityMeasure (ν i)]
    (ht : ∀ x, (q + ∑ i, p i * u i x) ≠ ∞) :
    (μ.withDensity (fun x => q + ∑ i, p i * u i x)) ⊗ₘ
        diagonalReplacementKernel q p u hu ν =
      q • μ.map (fun x => (x, x)) +
        ∑ i, p i • (μ.withDensity (u i)).prod (ν i) := by
  let κ : Option I → Kernel X X := fun o => match o with
    | none => Kernel.id
    | some i => Kernel.const X (ν i)
  let w : Option I → X → ℝ≥0∞ := fun o x => match o with
    | none => q
    | some i => p i * u i x
  have hw : ∀ o, Measurable (w o) := by
    intro o
    cases o with
    | none => exact measurable_const
    | some i => exact measurable_const.mul (hu i)
  have : ∀ o, IsMarkovKernel (κ o) := by
    intro o
    cases o <;> dsimp [κ] <;> infer_instance
  have h0 (x : X) : (∑ o, w o x) ≠ 0 := by
    intro h
    have h' : q + ∑ i, p i * u i x = 0 := by
      simpa only [Fintype.sum_option, w] using h
    exact hq (add_eq_zero.mp h').1
  have hfin (x : X) : (∑ o, w o x) ≠ ∞ := by
    simpa only [Fintype.sum_option, w] using ht x
  have hdis := normalizedKernel_disintegration μ κ w hw h0 hfin
  simp only [Fintype.sum_option, κ, w] at hdis
  change (μ.withDensity (fun x => q + ∑ i, p i * u i x)) ⊗ₘ
    diagonalReplacementKernel q p u hu ν = _ at hdis
  rw [hdis]
  congr 1
  · rw [withDensity_const, Measure.compProd_smul_left, Measure.compProd_id]
    rfl
  · apply Finset.sum_congr rfl
    intro i _
    rw [Measure.compProd_const]
    change (μ.withDensity (p i • u i)).prod (ν i) = _
    rw [withDensity_smul (p i) (hu i), Measure.prod_smul_left]

theorem diagonalReplacementKernel_event_lower (q : ℝ≥0∞) (p : I → ℝ≥0∞)
    (u : I → X → ℝ≥0∞) (hu : ∀ i, Measurable (u i))
    (ν : I → Measure X) (x : X) (s : Set X) (i : I) (C : ℝ≥0∞)
    (hui : 1 ≤ u i x) (hC : (q + ∑ j, p j * u j x) ≤ C)
    (hν : ν i s = 1) :
    p i / C ≤ diagonalReplacementKernel q p u hu ν x s := by
  classical
  rw [diagonalReplacementKernel_apply]
  simp only [Measure.add_apply, Measure.smul_apply, smul_eq_mul,
    Measure.finsetSum_apply]
  calc
    p i / C ≤ p i * u i x / (q + ∑ j, p j * u j x) := by
      apply ENNReal.div_le_div ?_ hC
      simpa only [mul_one] using mul_le_mul_right hui (p i)
    _ = (p i * u i x / (q + ∑ j, p j * u j x)) * ν i s := by rw [hν, mul_one]
    _ ≤ ∑ j, (p j * u j x / (q + ∑ k, p k * u k x)) * ν j s :=
      Finset.single_le_sum
        (f := fun j => (p j * u j x / (q + ∑ k, p k * u k x)) * ν j s)
        (fun _ _ => bot_le) (Finset.mem_univ i)
    _ ≤ _ := le_add_self

end Invariant233.FiniteKernelMixture

end OAI
