import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralRegularOperator

namespace OAI

/-! A bounded evaluation of the derivative kernel, for holomorphic regular spectral jets. -/

open Set
open scoped BoundedContinuousFunction
namespace DefocusingNLS

theorem spectralRegularWeightedSource_add (α : ℝ) (f g : ℝ →ᵇ ℂ) :
    spectralRegularWeightedSource α (f+g)=
      fun s => spectralRegularWeightedSource α f s+spectralRegularWeightedSource α g s := by
  funext s
  simp only [spectralRegularWeightedSource,BoundedContinuousFunction.add_apply,mul_add]

theorem spectralRegularWeightedSource_smul (α : ℝ) (a : ℂ) (f : ℝ →ᵇ ℂ) :
    spectralRegularWeightedSource α (a • f)=fun s => a*spectralRegularWeightedSource α f s := by
  funext s
  simp only [spectralRegularWeightedSource,BoundedContinuousFunction.smul_apply,smul_eq_mul]
  ring

noncomputable def spectralRegularAverageCLM (d : ℕ) (h α r : ℝ)
    (hα : 0 ≤ α) (hr : 0 ≤ r) : (ℝ →ᵇ ℂ) →L[ℂ] ℂ :=
  LinearMap.mkContinuous
    { toFun := fun f => spectralRegularAverage d h (spectralRegularWeightedSource α f) r
      map_add' := by
        intro f g
        rw [spectralRegularWeightedSource_add,spectralRegularAverage_add d h _ _
          (spectralRegularWeightedSource_continuous α f)
          (spectralRegularWeightedSource_continuous α g)]
      map_smul' := by
        intro a f
        change spectralRegularAverage d h (spectralRegularWeightedSource α (a • f)) r=
          a*spectralRegularAverage d h (spectralRegularWeightedSource α f) r
        rw [spectralRegularWeightedSource_smul,spectralRegularAverage_smul] }
    (Real.exp (α*r^2)) (fun f => by
      change ‖spectralRegularAverage d h (spectralRegularWeightedSource α f) r‖ ≤ _
      rw [mul_comm]
      exact spectralRegularAverage_weighted_bound d h r α ‖f‖ r hα (norm_nonneg _)
        ⟨hr,le_rfl⟩ _ (fun s _ => spectralRegularWeightedSource_bound α f s))

end DefocusingNLS

end OAI
