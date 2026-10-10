import OAI.Analysis.IrrationalRotation.Analysis.ScalarMultiplier
import OAI.Analysis.IrrationalRotation.Analysis.ContinuousLpInfinityNorm

namespace OAI

open MeasureTheory Filter
open scoped ENNReal

namespace Invariant233.L2Multiplication

variable {X E : Type*} [MeasurableSpace X] {μ : Measure X}
  [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem norm_compLp_unitVector (e : E) (he : ‖e‖ = 1) (f : Lp ℂ 2 μ) :
    ‖(ContinuousLinearMap.toSpanSingleton ℂ e).compLp f‖ = ‖f‖ := by
  rw [Lp.norm_def, Lp.norm_def]
  congr 1
  apply eLpNorm_congr_norm_ae (Lp.aestronglyMeasurable _) (Lp.aestronglyMeasurable f)
  filter_upwards [(ContinuousLinearMap.toSpanSingleton ℂ e).coeFn_compLp f] with x hx
  rw [hx]
  simp [norm_smul, he]

theorem multiplier_compLp_unitVector (g : Lp ℂ ∞ μ) (e : E) (f : Lp ℂ 2 μ) :
    multiplier g ((ContinuousLinearMap.toSpanSingleton ℂ e).compLp f) =
      (ContinuousLinearMap.toSpanSingleton ℂ e).compLp (multiplier g f) := by
  apply Lp.ext
  filter_upwards [multiplier_coe g ((ContinuousLinearMap.toSpanSingleton ℂ e).compLp f),
    (ContinuousLinearMap.toSpanSingleton ℂ e).coeFn_compLp f,
    (ContinuousLinearMap.toSpanSingleton ℂ e).coeFn_compLp (multiplier g f),
    multiplier_coe g f] with x hmul hemb hresult hscalar
  rw [hmul, hemb, hresult, hscalar]
  simp [smul_smul]

theorem norm_multiplier_eq_of_unitVector [IsFiniteMeasure μ]
    (g : Lp ℂ ∞ μ) (e : E) (he : ‖e‖ = 1) :
    ‖(multiplier g : Lp E 2 μ →L[ℂ] Lp E 2 μ)‖ = ‖g‖ := by
  apply le_antisymm (norm_multiplier_le g)
  rw [← norm_scalar_multiplier g]
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro f
  rw [← norm_compLp_unitVector e he (multiplier g f),
    ← multiplier_compLp_unitVector]
  calc
    ‖multiplier g ((ContinuousLinearMap.toSpanSingleton ℂ e).compLp f)‖ ≤
        ‖(multiplier g : Lp E 2 μ →L[ℂ] Lp E 2 μ)‖ *
          ‖(ContinuousLinearMap.toSpanSingleton ℂ e).compLp f‖ :=
      (multiplier (E := E) g).le_opNorm ((ContinuousLinearMap.toSpanSingleton ℂ e).compLp f)
    _ = _ := by rw [norm_compLp_unitVector e he]


variable [TopologicalSpace X] [BorelSpace X] [CompactSpace X]
  [IsFiniteMeasure μ] [μ.IsOpenPosMeasure]

theorem norm_continuous_scalar_multiplier (f : C(X, ℂ)) :
    ‖(multiplier (ContinuousMap.toLp ∞ μ ℂ f) : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ)‖ =
      ‖f‖ := by
  rw [norm_scalar_multiplier, Invariant233.norm_continuous_toLp_top]

theorem norm_continuous_multiplier (f : C(X, ℂ)) (e : E) (he : ‖e‖ = 1) :
    ‖(multiplier (ContinuousMap.toLp ∞ μ ℂ f) : Lp E 2 μ →L[ℂ] Lp E 2 μ)‖ =
      ‖f‖ := by
  rw [norm_multiplier_eq_of_unitVector _ e he, Invariant233.norm_continuous_toLp_top]

end Invariant233.L2Multiplication

end OAI
