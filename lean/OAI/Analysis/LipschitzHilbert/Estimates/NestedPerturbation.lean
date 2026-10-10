import OAI.Analysis.LipschitzHilbert.Estimates.NestedAverage
import OAI.Analysis.LipschitzHilbert.Estimates.ProductPerturbation
import OAI.Analysis.LipschitzHilbert.Trees.PathDrops
import Mathlib.Algebra.BigOperators.Fin

namespace OAI

/-! Nested prediction products with an explicit total logarithmic-error budget. -/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace LipschitzHilbert

variable {α κ : Type*} [MeasurableSpace α] [Fintype κ]

theorem nested_perturbed_product_le (μ : Measure α) [IsFiniteMeasure μ]
    (P : ℕ → α → κ) (R : ℕ → κ → κ) (g : ℕ → κ → ℝ)
    (β e : ℕ → α → ℝ) (N : ℕ) (B : ℝ)
    (hP : ∀ n ≤ N, ∀ i, MeasurableSet {x | P n x = i})
    (hrefine : ∀ n < N, ∀ x, P n x = R n (P (n + 1) x))
    (hg : ∀ n < N, ∀ i, 0 ≤ g n i)
    (haverage : ∀ n < N, ∀ i,
      (∫ x in {x | P n x = i}, g n (P (n + 1) x) ∂μ) ≤ μ.real {x | P n x = i})
    (hβmeas : ∀ j < N, Measurable (β j))
    (hβ : ∀ᵐ x ∂μ, ∀ j < N, 0 ≤ β j x)
    (hcomparison : ∀ᵐ x ∂μ, ∀ j < N, β j x ≤ Real.exp (e j x) * g j (P (j + 1) x))
    (hbudget : ∀ᵐ x ∂μ, (∑ j ∈ Finset.range N, e j x) ≤ B) :
    (∫ x, ∏ j ∈ Finset.range N, β j x ∂μ) ≤ Real.exp B * μ.real Set.univ := by
  have hgint : Integrable (fun x => ∏ i : Fin N, g i.val (P (i.val + 1) x)) μ := by
    simpa only [Finset.prod_range] using
      integrable_nested_product μ P R g N (hP N le_rfl) hrefine
  have hav : (∫ x, ∏ i : Fin N, g i.val (P (i.val + 1) x) ∂μ) ≤ μ.real Set.univ := by
    simpa only [Finset.prod_range] using
      nested_average_product_le μ P R g N hP hrefine hg haverage
  have hβ' : ∀ᵐ x ∂μ, ∀ i : Fin N, 0 ≤ β i.val x := by
    filter_upwards [hβ] with x hx i
    exact hx i.val i.isLt
  have hg' : ∀ᵐ x ∂μ, ∀ i : Fin N, 0 ≤ g i.val (P (i.val + 1) x) :=
    Filter.Eventually.of_forall (fun _ i => hg i.val i.isLt _)
  have hcmp : ∀ᵐ x ∂μ, ∀ i : Fin N,
      β i.val x ≤ Real.exp (e i.val x) * g i.val (P (i.val + 1) x) := by
    filter_upwards [hcomparison] with x hx i
    exact hx i.val i.isLt
  have hsum : ∀ᵐ x ∂μ, (∑ i : Fin N, e i.val x) ≤ B := by
    simpa only [Finset.sum_range] using hbudget
  have h := integral_perturbed_product_le μ (fun i : Fin N => β i.val)
    (fun i : Fin N => fun x => g i.val (P (i.val + 1) x)) (fun i : Fin N => e i.val)
    (μ.real Set.univ) B (fun i => hβmeas i.val i.isLt) hgint hβ' hg' hcmp hsum hav
  simpa only [Finset.prod_range] using h

omit [MeasurableSpace α] [Fintype κ] in
theorem stopped_error_budget (n e : ℕ → ℝ) (N stop : ℕ) (hstop : stop ≤ N)
    {M C L : ℝ} (hM : 0 < M) (hC : 0 ≤ C)
    (hactive : ∀ j < stop, M < n j) (hlast : 0 ≤ n stop)
    (hlog : max 0 (Real.log (n 0 / M)) ≤ L)
    (he : ∀ j < N, e j ≤ if j < stop then C * pathDrop n j else 0) :
    (∑ j ∈ Finset.range N, e j) ≤ C * (1 + L) := by
  have hfilter : (Finset.range N).filter (fun j => j < stop) = Finset.range stop := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  calc
    _ ≤ ∑ j ∈ Finset.range N, if j < stop then C * pathDrop n j else 0 :=
      Finset.sum_le_sum (fun j hj => he j (Finset.mem_range.mp hj))
    _ = C * ∑ j ∈ Finset.range stop, pathDrop n j := by
      rw [← Finset.sum_filter, hfilter, Finset.mul_sum]
    _ ≤ C * (1 + max 0 (Real.log (n 0 / M))) :=
      mul_le_mul_of_nonneg_left (active_path_drop_budget n stop hM hactive hlast) hC
    _ ≤ _ := mul_le_mul_of_nonneg_left (add_le_add le_rfl hlog) hC

end LipschitzHilbert

end

end OAI
