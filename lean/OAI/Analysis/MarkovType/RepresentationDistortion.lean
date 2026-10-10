import OAI.Analysis.MarkovType.FinitelyRepresentable
import Mathlib.Analysis.Normed.Module.FiniteDimension

namespace OAI

noncomputable section

namespace MarkovSuperreflexivity

universe u v
variable {X : Type u} {Y : Type v}
variable [NormedAddCommGroup X] [NormedSpace ℝ X]
variable [NormedAddCommGroup Y] [NormedSpace ℝ Y]

theorem FinitelyRepresentable.strict_distortion (h : FinitelyRepresentable Y X)
    (E : Submodule ℝ Y) [FiniteDimensional ℝ E] {η : ℝ} (hη : 0 < η) :
    ∃ (F : Submodule ℝ X) (e : E ≃L[ℝ] F),
      ‖e.toContinuousLinearMap‖ * ‖e.symm.toContinuousLinearMap‖ < 1 + η := by
  obtain ⟨T, hT⟩ := h E (η / 2) (by linarith)
  have hTi : Function.Injective T :=
    FinitelyRepresentable.injective_of_lower_bound T (fun z => (hT z).1)
  let F : Submodule ℝ X := LinearMap.range T
  let : FiniteDimensional ℝ F := LinearMap.finiteDimensional_range T
  let e : E ≃L[ℝ] F := (LinearEquiv.ofInjective T hTi).toContinuousLinearEquiv
  have hforward (z : E) : ‖e z‖ = ‖T z‖ := rfl
  have hupper : ‖e.toContinuousLinearMap‖ ≤ 1 + η / 2 := by
    apply e.toContinuousLinearMap.opNorm_le_bound (by linarith)
    intro z
    change ‖e z‖ ≤ (1 + η / 2) * ‖z‖
    rw [hforward]
    exact (hT z).2
  have hinverse : ‖e.symm.toContinuousLinearMap‖ ≤ 1 := by
    apply e.symm.toContinuousLinearMap.opNorm_le_bound zero_le_one
    intro z
    change ‖e.symm z‖ ≤ 1 * ‖z‖
    rw [one_mul]
    calc
      ‖e.symm z‖ ≤ ‖T (e.symm z)‖ := (hT _).1
      _ = ‖e (e.symm z)‖ := (hforward _).symm
      _ = ‖z‖ := congrArg norm (e.apply_symm_apply z)
  refine ⟨F, e, ?_⟩
  calc
    ‖e.toContinuousLinearMap‖ * ‖e.symm.toContinuousLinearMap‖
        ≤ (1 + η / 2) * 1 :=
      mul_le_mul hupper hinverse (norm_nonneg e.symm.toContinuousLinearMap) (by linarith)
    _ < 1 + η := by linarith

end MarkovSuperreflexivity

end

end OAI
