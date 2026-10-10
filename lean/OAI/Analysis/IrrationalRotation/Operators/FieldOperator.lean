import OAI.Analysis.IrrationalRotation.Model.FieldOperator
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.Tactic

namespace OAI

noncomputable section
open MeasureTheory Filter TopologicalSpace
open scoped ENNReal Topology

namespace Invariant233.DirectIntegral
variable {X E F G : Type*} [MeasurableSpace X] {μ : Measure X}
  [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]
  [NormedAddCommGroup G] [NormedSpace ℂ G]

variable (A : X → E →L[ℂ] F) (C : ℝ)
  (hA : ∀ x, ‖A x‖ ≤ C)
  (hm : ∀ v, AEStronglyMeasurable (fun x => A x v) μ)

theorem fieldOperator_ae (f : Lp E 2 μ) :
    fieldOperator A C hA hm f =ᵐ[μ] fun x => A x (f x) :=
  fieldOperatorVec_ae A C hA hm f

theorem norm_fieldOperator_le (hC : 0 ≤ C) : ‖fieldOperator A C hA hm‖ ≤ C :=
  LinearMap.mkContinuous_norm_le _ hC _

variable {A C hA hm}

theorem fieldOperator_congr
    {B : X → E →L[ℂ] F} {D : ℝ} {hB : ∀ x, ‖B x‖ ≤ D}
    {hn : ∀ v, AEStronglyMeasurable (fun x => B x v) μ}
    (heq : A =ᵐ[μ] B) : fieldOperator A C hA hm = fieldOperator B D hB hn := by
  ext f
  filter_upwards [fieldOperator_ae A C hA hm f,
    fieldOperator_ae B D hB hn f, heq] with x hx hy hxy
  rw [hx, hy, hxy]

theorem fieldOperator_comp_of_ae_eq
    {B : X → F →L[ℂ] G} {P : X → E →L[ℂ] G} {D R : ℝ}
    {hB : ∀ x, ‖B x‖ ≤ D} {hP : ∀ x, ‖P x‖ ≤ R}
    {hn : ∀ v, AEStronglyMeasurable (fun x => B x v) μ}
    {hp : ∀ v, AEStronglyMeasurable (fun x => P x v) μ}
    (heq : P =ᵐ[μ] fun x => (B x).comp (A x)) :
    fieldOperator P R hP hp =
      (fieldOperator B D hB hn).comp (fieldOperator A C hA hm) := by
  ext f
  filter_upwards [fieldOperator_ae P R hP hp f,
    fieldOperator_ae B D hB hn (fieldOperator A C hA hm f),
    fieldOperator_ae A C hA hm f, heq] with x hx hy hz he
  change fieldOperator P R hP hp f x =
    fieldOperator B D hB hn (fieldOperator A C hA hm f) x
  rw [hx, hy, hz, he]
  rfl

theorem fieldOperator_ae_eq_of_eq [IsFiniteMeasure μ] [SeparableSpace E]
    {B : X → E →L[ℂ] F} {D : ℝ} {hB : ∀ x, ‖B x‖ ≤ D}
    {hn : ∀ v, AEStronglyMeasurable (fun x => B x v) μ}
    (heq : fieldOperator A C hA hm = fieldOperator B D hB hn) : A =ᵐ[μ] B := by
  have hpoint (v : E) : ∀ᵐ x ∂μ, A x v = B x v := by
    have heqv := congrArg (fun T : Lp E 2 μ →L[ℂ] Lp F 2 μ => T (Lp.const 2 μ v)) heq
    have hae : fieldOperator A C hA hm (Lp.const 2 μ v) =ᵐ[μ]
        fieldOperator B D hB hn (Lp.const 2 μ v) := by rw [heqv]
    filter_upwards [fieldOperator_ae A C hA hm (Lp.const 2 μ v),
      fieldOperator_ae B D hB hn (Lp.const 2 μ v), Lp.coeFn_const 2 μ v, hae]
      with x hx hy hv he
    simpa only [hx, hy, hv, Function.const_apply] using he
  have hseq : ∀ᵐ x ∂μ, ∀ n : ℕ, A x (denseSeq E n) = B x (denseSeq E n) :=
    ae_all_iff.mpr fun n => hpoint (denseSeq E n)
  filter_upwards [hseq] with x hx
  have hfunctions : (A x : E → F) = (B x : E → F) :=
    (denseRange_denseSeq E).equalizer (A x).continuous (B x).continuous (funext hx)
  exact DFunLike.ext' hfunctions

end Invariant233.DirectIntegral

namespace Invariant233.DirectIntegral
variable {X E F : Type*} [MeasurableSpace X] {μ : Measure X}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  {A : X → E →L[ℂ] F} {C : ℝ} {hA : ∀ x, ‖A x‖ ≤ C}
  {hm : ∀ v, AEStronglyMeasurable (fun x => A x v) μ}

theorem fieldOperator_adjoint_of_ae_eq
    {B : X → F →L[ℂ] E} {D : ℝ} {hB : ∀ x, ‖B x‖ ≤ D}
    {hn : ∀ v, AEStronglyMeasurable (fun x => B x v) μ}
    (heq : B =ᵐ[μ] fun x => ContinuousLinearMap.adjoint (A x)) :
    fieldOperator B D hB hn = ContinuousLinearMap.adjoint (fieldOperator A C hA hm) := by
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).2
  intro f g
  simp only [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [fieldOperator_ae B D hB hn f,
    fieldOperator_ae A C hA hm g, heq] with x hx hy he
  rw [hx, hy, he]
  exact (A x).adjoint_inner_left (g x) (f x)

end Invariant233.DirectIntegral

end

end OAI
