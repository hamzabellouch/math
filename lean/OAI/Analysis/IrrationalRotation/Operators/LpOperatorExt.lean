import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
import Mathlib.Analysis.InnerProductSpace.l2Space

namespace OAI

namespace Invariant233.Fields

open MeasureTheory
open scoped ENNReal

variable {X E F : Type*} [MeasurableSpace X] [NormedAddCommGroup E]
  [NormedSpace ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F]
  {μ : Measure X} {p : ℝ≥0∞} [Fact (1 ≤ p)]

theorem lp_operator_ext_indicator (hp : p ≠ ∞)
    (A B : Lp E p μ →L[ℂ] F)
    (h : ∀ (v : E) (s : Set X) (hs : MeasurableSet s) (hμs : μ s ≠ ∞),
      A (indicatorConstLp p hs hμs v) = B (indicatorConstLp p hs hμs v)) :
    A = B := by
  ext f
  apply Lp.induction hp (fun g => A g = B g) _ _ _ f
  · intro v s hs hμs
    exact h v s hs hμs.ne
  · intro g k hg hk hdis hAg hAk
    simp only [map_add, hAg, hAk]
  · exact isClosed_eq A.continuous B.continuous

noncomputable def indicatorConstLpCLM (s : Set X) (hs : MeasurableSet s)
    (hμs : μ s ≠ ∞) : E →L[ℂ] Lp E p μ :=
  LinearMap.mkContinuous
    { toFun := indicatorConstLp p hs hμs
      map_add' := fun v w => (indicatorConstLp_add (c := v) (c' := w)).symm
      map_smul' := by
        intro c v
        simp only [indicatorConstLp, ← MemLp.toLp_const_smul]
        apply MemLp.toLp_congr
        exact Filter.Eventually.of_forall fun x => by
          simp only [RingHom.id_apply, Pi.smul_apply, Set.indicator_smul_apply] }
    (μ.real s ^ (1 / p.toReal))
    (fun v => by
      change ‖indicatorConstLp p hs hμs v‖ ≤ μ.real s ^ (1 / p.toReal) * ‖v‖
      simpa only [mul_comm] using
        (norm_indicatorConstLp_le (p := p) (hs := hs) (hμs := hμs) (c := v)))

theorem lp_operator_ext_basis_indicator {H ι : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (e : HilbertBasis ι ℂ H) (hp : p ≠ ∞)
    (A B : Lp H p μ →L[ℂ] F)
    (h : ∀ (i : ι) (s : Set X) (hs : MeasurableSet s) (hμs : μ s ≠ ∞),
      A (indicatorConstLp p hs hμs (e i)) =
        B (indicatorConstLp p hs hμs (e i))) : A = B := by
  apply lp_operator_ext_indicator hp A B
  intro v s hs hμs
  let C : H →L[ℂ] Lp H p μ := indicatorConstLpCLM s hs hμs
  have hAC : A.comp C = B.comp C := by
    apply ContinuousLinearMap.ext_on
      (Submodule.dense_iff_topologicalClosure_eq_top.mpr e.dense_span)
    rintro _ ⟨i, rfl⟩
    exact h i s hs hμs
  exact DFunLike.congr_fun hAC v

end Invariant233.Fields

end OAI
