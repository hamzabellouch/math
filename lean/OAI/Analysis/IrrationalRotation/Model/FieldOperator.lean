import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Lemmas

namespace OAI

noncomputable section
open MeasureTheory Filter
open scoped ENNReal Topology

namespace Invariant233.DirectIntegral
variable {X E F : Type*} [MeasurableSpace X] {μ : Measure X}
  [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

theorem apply_simple_aestronglyMeasurable
    (A : X → E →L[ℂ] F)
    (hm : ∀ v, AEStronglyMeasurable (fun x => A x v) μ) (s : SimpleFunc X E) :
    AEStronglyMeasurable (fun x => A x (s x)) μ := by
  classical
  induction s using SimpleFunc.induction' with
  | const v => exact hm v
  | @pcw s t u hu hs ht =>
    convert AEStronglyMeasurable.piecewise hu hs.restrict ht.restrict using 1
    funext x
    by_cases hx : x ∈ u <;> simp [SimpleFunc.coe_piecewise, hx]

theorem apply_aestronglyMeasurable
    (A : X → E →L[ℂ] F)
    (hm : ∀ v, AEStronglyMeasurable (fun x => A x v) μ)
    {f : X → E} (hf : AEStronglyMeasurable f μ) :
    AEStronglyMeasurable (fun x => A x (f x)) μ := by
  apply aestronglyMeasurable_of_tendsto_ae atTop
    (f := fun n x => A x (hf.stronglyMeasurable_mk.approx n x))
  · intro n
    exact apply_simple_aestronglyMeasurable A hm _
  · filter_upwards [hf.ae_eq_mk] with x hx
    rw [hx]
    exact ((A x).continuous.tendsto _).comp (hf.stronglyMeasurable_mk.tendsto_approx x)

def fieldOperatorVec (A : X → E →L[ℂ] F) (C : ℝ)
    (hA : ∀ x, ‖A x‖ ≤ C)
    (hm : ∀ v, AEStronglyMeasurable (fun x => A x v) μ)
    (f : Lp E 2 μ) : Lp F 2 μ :=
  ((Lp.memLp f).of_le_mul (apply_aestronglyMeasurable A hm (Lp.aestronglyMeasurable f))
    (Filter.Eventually.of_forall fun x => (A x).le_of_opNorm_le (hA x) (f x))).toLp _

theorem fieldOperatorVec_ae (A : X → E →L[ℂ] F) (C : ℝ)
    (hA : ∀ x, ‖A x‖ ≤ C)
    (hm : ∀ v, AEStronglyMeasurable (fun x => A x v) μ)
    (f : Lp E 2 μ) :
    fieldOperatorVec A C hA hm f =ᵐ[μ] fun x => A x (f x) :=
  MemLp.coeFn_toLp _

def fieldOperatorLinear (A : X → E →L[ℂ] F) (C : ℝ)
    (hA : ∀ x, ‖A x‖ ≤ C)
    (hm : ∀ v, AEStronglyMeasurable (fun x => A x v) μ) :
    Lp E 2 μ →ₗ[ℂ] Lp F 2 μ where
  toFun := fieldOperatorVec A C hA hm
  map_add' f g := by
    apply Lp.ext
    filter_upwards [fieldOperatorVec_ae A C hA hm (f + g),
      fieldOperatorVec_ae A C hA hm f, fieldOperatorVec_ae A C hA hm g,
      Lp.coeFn_add f g,
      Lp.coeFn_add (fieldOperatorVec A C hA hm f) (fieldOperatorVec A C hA hm g)]
      with x hfg hf hg hsum hout
    simp only [Pi.add_apply] at hsum hout
    rw [hfg, hout, hf, hg, hsum, map_add]
  map_smul' c f := by
    change fieldOperatorVec A C hA hm (c • f) = c • fieldOperatorVec A C hA hm f
    apply Lp.ext
    filter_upwards [fieldOperatorVec_ae A C hA hm (c • f),
      fieldOperatorVec_ae A C hA hm f, Lp.coeFn_smul c f,
      Lp.coeFn_smul c (fieldOperatorVec A C hA hm f)] with x hcf hf hsmul hout
    simp only [Pi.smul_apply] at hsmul hout
    rw [hcf, hout, hf, hsmul, map_smul]

def fieldOperator (A : X → E →L[ℂ] F) (C : ℝ)
    (hA : ∀ x, ‖A x‖ ≤ C)
    (hm : ∀ v, AEStronglyMeasurable (fun x => A x v) μ) :
    Lp E 2 μ →L[ℂ] Lp F 2 μ :=
  (fieldOperatorLinear A C hA hm).mkContinuous C (by
    intro f
    apply Lp.norm_le_mul_norm_of_ae_le_mul
    change ∀ᵐ x ∂μ, ‖fieldOperatorVec A C hA hm f x‖ ≤ C * ‖f x‖
    filter_upwards [fieldOperatorVec_ae A C hA hm f] with x hx
    rw [hx]
    exact (A x).le_of_opNorm_le (hA x) (f x))

end Invariant233.DirectIntegral

end

end OAI
