import OAI.Analysis.IrrationalRotation.Analysis.FieldVectorState
import Mathlib.MeasureTheory.Function.AEEqOfIntegral

namespace OAI

open MeasureTheory Filter
open scoped InnerProductSpace Topology ComplexOrder

namespace Invariant233.FieldTraceCyclic

variable {Ω E : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  {μ : Measure Ω} [IsFiniteMeasure μ]

theorem indicator_quadratic_eq_setIntegral
    (T : Lp E 2 μ →L[ℂ] Lp E 2 μ) (A : Ω → E →L[ℂ] E)
    (hT : ∀ ξ : Lp E 2 μ, ∀ᵐ x ∂μ, (T ξ) x = A x (ξ x))
    (v : E) (s : Set Ω) (hs : MeasurableSet s) :
    inner ℂ (T (indicatorConstLp 2 hs (measure_ne_top μ s) v))
      (indicatorConstLp 2 hs (measure_ne_top μ s) v) =
        ∫ x in s, inner ℂ (A x v) v ∂μ := by
  rw [L2.inner_def, ← integral_indicator hs]
  apply integral_congr_ae
  filter_upwards [indicatorConstLp_coeFn (p := 2) (hs := hs)
      (hμs := measure_ne_top μ s) (c := v),
    hT (indicatorConstLp 2 hs (measure_ne_top μ s) v)] with x hx hTx
  rw [hTx, hx]
  by_cases hxs : x ∈ s
  · simp only [Set.indicator_of_mem hxs]
  · simp only [Set.indicator_of_notMem hxs, map_zero, inner_zero_left]

theorem integrable_represented_quadratic
    (T : Lp E 2 μ →L[ℂ] Lp E 2 μ) (A : Ω → E →L[ℂ] E)
    (hT : ∀ ξ : Lp E 2 μ, ∀ᵐ x ∂μ, (T ξ) x = A x (ξ x)) (v : E) :
    Integrable (fun x => inner ℂ (A x v) v) μ := by
  apply (L2.integrable_inner (𝕜 := ℂ) (T (Lp.const 2 μ v))
    (Lp.const 2 μ v)).congr
  filter_upwards [Lp.coeFn_const 2 μ v, hT (Lp.const 2 μ v)] with x hx hTx
  rw [hTx, hx]
  rfl

theorem ae_represented_quadratic_nonneg
    (T : Lp E 2 μ →L[ℂ] Lp E 2 μ) (A : Ω → E →L[ℂ] E)
    (hT : ∀ ξ : Lp E 2 μ, ∀ᵐ x ∂μ, (T ξ) x = A x (ξ x))
    (hpos : T.IsPositive) (v : E) :
    ∀ᵐ x ∂μ, 0 ≤ (inner ℂ (A x v) v).re ∧ (inner ℂ (A x v) v).im = 0 := by
  have hi := integrable_represented_quadratic T A hT v
  have hlocal (s : Set Ω) (hs : MeasurableSet s) :
      0 ≤ ∫ x in s, inner ℂ (A x v) v ∂μ := by
    rw [← indicator_quadratic_eq_setIntegral T A hT v s hs]
    exact hpos.inner_nonneg_left _
  have hreal : 0 ≤ᵐ[μ] fun x => (inner ℂ (A x v) v).re := by
    apply ae_nonneg_of_forall_setIntegral_nonneg hi.re
    intro s hs _
    rw [integral_re hi.integrableOn]
    exact (Complex.nonneg_iff.mp (hlocal s hs)).1
  have him : (fun x => (inner ℂ (A x v) v).im) =ᵐ[μ] 0 := by
    apply hi.im.ae_eq_zero_of_forall_setIntegral_eq_zero
    intro s hs _
    rw [integral_im hi.integrableOn]
    exact (Complex.nonneg_iff.mp (hlocal s hs)).2.symm
  filter_upwards [hreal, him] with x hr hm
  exact ⟨hr, hm⟩

theorem ae_isPositive_of_represented_isPositive [TopologicalSpace.SeparableSpace E]
    (T : Lp E 2 μ →L[ℂ] Lp E 2 μ) (A : Ω → E →L[ℂ] E)
    (hT : ∀ ξ : Lp E 2 μ, ∀ᵐ x ∂μ, (T ξ) x = A x (ξ x))
    (hpos : T.IsPositive) : ∀ᵐ x ∂μ, (A x).IsPositive := by
  let v := TopologicalSpace.denseSeq E
  have hv : DenseRange v := TopologicalSpace.denseRange_denseSeq E
  have hall : ∀ᵐ x ∂μ, ∀ n : ℕ,
      0 ≤ (inner ℂ (A x (v n)) (v n)).re ∧
        (inner ℂ (A x (v n)) (v n)).im = 0 :=
    ae_all_iff.mpr (fun n => ae_represented_quadratic_nonneg T A hT hpos (v n))
  filter_upwards [hall] with x hx
  apply (ContinuousLinearMap.isPositive_iff_complex (A x)).mpr
  intro w
  have hc : Continuous (fun w => inner ℂ (A x w) w) :=
    (A x).continuous.inner continuous_id
  have hm : 0 ≤ (inner ℂ (A x w) w).re ∧ (inner ℂ (A x w) w).im = 0 :=
    hv.induction_on w
      ((isClosed_le continuous_const (Complex.continuous_re.comp hc)).inter
        (isClosed_eq (Complex.continuous_im.comp hc) continuous_const)) hx
  refine ⟨?_, hm.1⟩
  apply Complex.ext
  · simp
  · simpa using hm.2.symm

end Invariant233.FieldTraceCyclic

end OAI
