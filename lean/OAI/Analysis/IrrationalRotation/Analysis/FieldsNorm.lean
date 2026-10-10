import Mathlib.MeasureTheory.Function.AEEqOfIntegral
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Topology.DenseEmbedding
import Mathlib.Tactic

namespace OAI

open MeasureTheory Filter Set

namespace Invariant233.Fields

variable {Y : Type*} [MeasurableSpace Y] {μ : Measure Y}

theorem ae_norm_le_of_local_square_integral [IsFiniteMeasure μ]
    {E : Type*} [NormedAddCommGroup E] {v : Y → E} {C : ℝ}
    (hC : 0 ≤ C) (hv : Integrable (fun y => ‖v y‖ ^ 2) μ)
    (hlocal : ∀ s, MeasurableSet s →
      (∫ y in s, ‖v y‖ ^ 2 ∂μ) ≤ C ^ 2 * μ.real s) :
    ∀ᵐ y ∂μ, ‖v y‖ ≤ C := by
  have hsq : (fun y => ‖v y‖ ^ 2) ≤ᵐ[μ] (fun _ => C ^ 2) := by
    apply ae_le_of_forall_setIntegral_le hv (integrable_const _)
    intro s hs _
    simpa only [setIntegral_const, smul_eq_mul, mul_comm] using hlocal s hs
  filter_upwards [hsq] with y hy
  nlinarith [norm_nonneg (v y)]


variable {𝕜 E F ι : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedAddCommGroup F]
    [NormedSpace 𝕜 E] [NormedSpace 𝕜 F] [Countable ι]

theorem ae_eq_of_countable_columns {A B : Y → E →L[𝕜] F} {v : ι → E}
    (hv : Dense (Submodule.span 𝕜 (Set.range v) : Set E))
    (hcol : ∀ i, ∀ᵐ y ∂μ, A y (v i) = B y (v i)) :
    A =ᵐ[μ] B := by
  have hcols : ∀ᵐ y ∂μ, ∀ i, A y (v i) = B y (v i) :=
    ae_all_iff.mpr hcol
  filter_upwards [hcols] with y hy
  apply ContinuousLinearMap.ext_on hv
  rintro _ ⟨i, rfl⟩
  exact hy i

theorem ae_opNorm_le_of_countable_dense {A : Y → E →L[𝕜] F} {v : ι → E}
    (hv : DenseRange v) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ i, ∀ᵐ y ∂μ, ‖A y (v i)‖ ≤ C * ‖v i‖) :
    ∀ᵐ y ∂μ, ‖A y‖ ≤ C := by
  have hall : ∀ᵐ y ∂μ, ∀ i, ‖A y (v i)‖ ≤ C * ‖v i‖ :=
    ae_all_iff.mpr hbound
  filter_upwards [hall] with y hy
  apply (A y).opNorm_le_bound hC
  intro x
  exact hv.induction_on (p := fun x => ‖A y x‖ ≤ C * ‖x‖) x
    (isClosed_le (A y).continuous.norm (continuous_const.mul continuous_norm)) hy


end Invariant233.Fields

end OAI
