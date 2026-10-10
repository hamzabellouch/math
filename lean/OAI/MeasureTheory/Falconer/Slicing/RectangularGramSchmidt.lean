import OAI.MeasureTheory.Falconer.Slicing.GramSchmidtMeasurable
import Mathlib.LinearAlgebra.Dimension.OrzechProperty
import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
import Mathlib.MeasureTheory.Function.SpecialFunctions.Inner

namespace OAI

/-! # Measurable Gram--Schmidt residuals with exact prefix dependence -/

namespace Falconer
open Set Submodule InnerProductSpace
variable {d m : ℕ}

theorem rectangular_gramSchmidt_measurable (i : Fin m) :
    Measurable (fun v : Fin m → Space d => gramSchmidt ℝ v i) := by
  induction i using WellFoundedLT.induction with
  | ind i ih =>
    have he : (fun v : Fin m → Space d => gramSchmidt ℝ v i) =
        fun v => v i - ∑ j ∈ Finset.Iio i, (ℝ ∙ gramSchmidt ℝ v j).starProjection (v i) :=
      funext (fun v => gramSchmidt_def ℝ v i)
    rw [he]
    simp_rw [starProjection_singleton]
    apply (measurable_pi_apply i).sub
    apply Finset.measurable_sum
    intro j hj
    have hg := ih j (Finset.mem_Iio.mp hj)
    change Measurable (fun v : Fin m → Space d =>
      (inner ℝ (gramSchmidt ℝ v j) (v i) / ‖gramSchmidt ℝ v j‖^2) • gramSchmidt ℝ v j)
    exact ((hg.inner (measurable_pi_apply i)).div (hg.norm.pow_const 2)).smul hg

theorem rectangular_gramSchmidt_prefix_congr (v w : Fin m → Space d) (i : Fin m)
    (h : ∀ j ≤ i, v j = w j) : gramSchmidt ℝ v i = gramSchmidt ℝ w i := by
  induction i using WellFoundedLT.induction with
  | ind i ih =>
    rw [gramSchmidt_def, gramSchmidt_def, h i le_rfl]
    congr 1
    apply Finset.sum_congr rfl
    intro j hj
    rw [ih j (Finset.mem_Iio.mp hj) (fun k hk => h k (hk.trans (Finset.mem_Iio.mp hj).le))]

theorem rectangular_independent_of_residuals (v : Fin m → Space d)
    (hv : ∀ i, gramSchmidt ℝ v i ≠ 0) : LinearIndependent ℝ v := by
  have hgs : LinearIndependent ℝ (gramSchmidt ℝ v) :=
    linearIndependent_of_ne_zero_of_inner_eq_zero hv (fun _ _ hij => gramSchmidt_orthogonal ℝ v hij)
  rw [linearIndependent_iff_card_eq_finrank_span]
  change Fintype.card (Fin m) = Module.finrank ℝ (span ℝ (range v))
  rw [← span_gramSchmidt ℝ v]
  exact (finrank_span_eq_card hgs).symm

theorem rectangular_zero_residual_mem_prefix (v : Fin m → Space d) (i : Fin m)
    (hz : gramSchmidt ℝ v i = 0) : v i ∈ span ℝ (v '' Iio i) := by
  rw [← span_gramSchmidt_Iio ℝ v i,gramSchmidt_def' ℝ v i,hz,zero_add]
  apply Submodule.sum_mem
  intro j hj
  simp only [starProjection_singleton]
  apply Submodule.smul_mem
  exact subset_span ⟨j,Finset.mem_Iio.mp hj,rfl⟩

end Falconer

end OAI
