import OAI.MeasureTheory.Falconer.Estimates.GeneralColumns
import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
import Mathlib.MeasureTheory.Function.SpecialFunctions.Inner

namespace OAI

/-! # Measurable Gram--Schmidt residuals with exact prefix dependence -/

namespace Falconer
open Set Submodule InnerProductSpace
variable {d : ℕ}

theorem gramSchmidt_measurable (i : Fin d) :
    Measurable (fun v : Fin d → Space d => gramSchmidt ℝ v i) := by
  induction i using WellFoundedLT.induction with
  | ind i ih =>
    have he : (fun v : Fin d → Space d => gramSchmidt ℝ v i) =
        fun v => v i - ∑ j ∈ Finset.Iio i, (ℝ ∙ gramSchmidt ℝ v j).starProjection (v i) :=
      funext (fun v => gramSchmidt_def ℝ v i)
    rw [he]
    simp_rw [starProjection_singleton]
    apply (measurable_pi_apply i).sub
    apply Finset.measurable_sum
    intro j hj
    have hg := ih j (Finset.mem_Iio.mp hj)
    change Measurable (fun v : Fin d → Space d =>
      (inner ℝ (gramSchmidt ℝ v j) (v i) / ‖gramSchmidt ℝ v j‖^2) • gramSchmidt ℝ v j)
    exact ((hg.inner (measurable_pi_apply i)).div (hg.norm.pow_const 2)).smul hg

theorem gramSchmidt_prefix_congr (v w : Fin d → Space d) (i : Fin d)
    (h : ∀ j ≤ i, v j = w j) : gramSchmidt ℝ v i = gramSchmidt ℝ w i := by
  induction i using WellFoundedLT.induction with
  | ind i ih =>
    rw [gramSchmidt_def, gramSchmidt_def, h i le_rfl]
    congr 1
    apply Finset.sum_congr rfl
    intro j hj
    rw [ih j (Finset.mem_Iio.mp hj) (fun k hk => h k (hk.trans (Finset.mem_Iio.mp hj).le))]

end Falconer

end OAI
