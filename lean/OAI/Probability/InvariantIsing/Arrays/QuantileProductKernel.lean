import OAI.Probability.InvariantIsing.Arrays.UltrametricProduct
import OAI.Probability.InvariantIsing.Core.Variational

namespace OAI

/-! Quantile form of the ultrametric product kernel, including plateaus. -/

noncomputable section

open MeasureTheory IsingPerceptron Set

namespace InvariantIsing

lemma quantile_product_kernel_eq (p : OverlapPath) (a b : ℝ → ℝ) (s u : ℝ) :
    replicaProductFirst a b (p s) (p u) + replicaProductSecond a b (p s) (p u) =
      if u < s then a (p u) * b (p u)
      else a (p u) * b (p s) + a (p s) * b (p u) - a (p s) * b (p s) := by
  by_cases hus : u < s
  · have hpu : p u ≤ p s := p.monotone hus.le
    rcases hpu.eq_or_lt with he | hlt
    · rw [he]
      simp [replicaProductFirst, replicaProductSecond, hus]
    · simp [replicaProductFirst, replicaProductSecond, hus, hlt, not_lt_of_ge hlt.le]
  · have hpu : p s ≤ p u := p.monotone (le_of_not_gt hus)
    rcases hpu.eq_or_lt with he | hlt
    · rw [he]
      simp [replicaProductFirst, replicaProductSecond, hus]
    · simp only [replicaProductFirst, replicaProductSecond, hus, hlt,
        not_lt_of_ge hlt.le, ↓reduceIte]
      ring

lemma intervalIntegrable_of_measurable_abs_le {f : ℝ → ℝ} (hf : Measurable f)
    {B : ℝ} (hb : ∀ u, |f u| ≤ B) (s t : ℝ) : IntervalIntegrable f volume s t := by
  rw [intervalIntegrable_iff]
  let : IsFiniteMeasure (volume.restrict (uIoc s t)) := by
    change IsFiniteMeasure (volume.restrict (Ioc (min s t) (max s t)))
    infer_instance
  exact integrable_of_measurable_abs_le hf hb

theorem integral_quantile_product_kernel (p : OverlapPath) (a b : ℝ → ℝ)
    (ha : Measurable a) (hb : Measurable b) {A B : ℝ} (hA : 0 ≤ A)
    (haB : ∀ x, |a x| ≤ A) (hbB : ∀ x, |b x| ≤ B)
    {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    (∫ u, replicaProductFirst a b (p s) (p u) + replicaProductSecond a b (p s) (p u) ∂pathMeasure) +
        a (p s) * b (p s) =
      (∫ u in 0..s, a (p u) * b (p u)) +
        b (p s) * (∫ u in s..1, a (p u)) +
        a (p s) * (∫ u in s..1, b (p u)) + s * (a (p s) * b (p s)) := by
  let f : ℝ → ℝ := fun u => a (p u)
  let g : ℝ → ℝ := fun u => b (p u)
  have hfm : Measurable f := ha.comp p.measurable
  have hgm : Measurable g := hb.comp p.measurable
  have hfg (u : ℝ) : |f u * g u| ≤ A * B := by
    rw [abs_mul]
    exact mul_le_mul (haB _) (hbB _) (abs_nonneg _) hA
  have hfi (v w : ℝ) : IntervalIntegrable f volume v w :=
    intervalIntegrable_of_measurable_abs_le hfm (fun u => haB _) v w
  have hgi (v w : ℝ) : IntervalIntegrable g volume v w :=
    intervalIntegrable_of_measurable_abs_le hgm (fun u => hbB _) v w
  have hfgi (v w : ℝ) : IntervalIntegrable (fun u => f u * g u) volume v w :=
    intervalIntegrable_of_measurable_abs_le (hfm.mul hgm) hfg v w
  let K : ℝ → ℝ := fun u => if u < s then f u * g u
    else f u * g s + f s * g u - f s * g s
  have hKi (v w : ℝ) : IntervalIntegrable K volume v w := by
    refine intervalIntegrable_of_measurable_abs_le (f := K) (B := 3 * (A * B)) ?_ ?_ v w
    · exact Measurable.ite (measurableSet_lt measurable_id measurable_const) (hfm.mul hgm)
        (((hfm.mul_const _).add (hgm.const_mul _)).sub measurable_const)
    intro u
    dsimp only [K]
    split_ifs
    · exact (hfg u).trans (by have := abs_nonneg (f u * g u); linarith [hfg u])
    · calc
        _ ≤ |f u * g s| + |f s * g u| + |f s * g s| :=
          (abs_sub _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
        _ ≤ 3 * (A * B) := by
          have h1 : |f u * g s| ≤ A * B := by
            rw [abs_mul]; exact mul_le_mul (haB _) (hbB _) (abs_nonneg _) hA
          have h2 : |f s * g u| ≤ A * B := by
            rw [abs_mul]; exact mul_le_mul (haB _) (hbB _) (abs_nonneg _) hA
          linarith [hfg s]
  have hlow : (∫ u in 0..s, K u) = ∫ u in 0..s, f u * g u := by
    apply intervalIntegral.integral_congr_Ioo_of_le hs.1
    intro u hu
    exact ite_eq_left hu.2
  have hhigh : (∫ u in s..1, K u) =
      g s * (∫ u in s..1, f u) + f s * (∫ u in s..1, g u) - (1 - s) * (f s * g s) := by
    calc
      _ = ∫ u in s..1, f u * g s + f s * g u - f s * g s := by
        apply intervalIntegral.integral_congr_Ioo_of_le hs.2
        intro u hu
        exact ite_eq_right (not_lt_of_ge hu.1.le)
      _ = _ := by
        rw [intervalIntegral.integral_sub ((hfi s 1).mul_const _ |>.add ((hgi s 1).const_mul _))
          intervalIntegrable_const,
          intervalIntegral.integral_add ((hfi s 1).mul_const _) ((hgi s 1).const_mul _),
          intervalIntegral.integral_mul_const, intervalIntegral.integral_const_mul,
          intervalIntegral.integral_const, smul_eq_mul]
        ring
  have hadd := intervalIntegral.integral_add_adjacent_intervals (hKi 0 s) (hKi s 1)
  rw [hlow, hhigh] at hadd
  simp_rw [quantile_product_kernel_eq]
  change (∫ u in Ioo 0 1, K u) + f s * g s = _
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le zero_le_one]
  dsimp only [f, g] at hadd ⊢
  linarith

end InvariantIsing

end

end OAI
