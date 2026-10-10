import OAI.Analysis.IrrationalRotation.Analysis.FejerBanachApproximation
import OAI.Analysis.IrrationalRotation.Rotation.RotationMeasurable

namespace OAI

noncomputable section
open MeasureTheory Filter
open scoped Topology BigOperators
namespace Invariant233
namespace StrongFourierRecovery

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def average (C : ℤ → H →L[ℂ] H) (N : ℕ) : H →L[ℂ] H :=
  ∑ r ∈ Fejer.frequencies N, Fejer.coefficient N r • C r

omit [CompleteSpace H] in

theorem average_apply
    (T : Fejer.Circle → H →L[ℂ] H)
    (hT : ∀ v : H, Continuous (fun t => T t v))
    (C : ℤ → H →L[ℂ] H)
    (hC : ∀ r v, C r v = ∫ t, fourier r t • T t v ∂AddCircle.haarAddCircle)
    (N : ℕ) (v : H) :
    average C N v = ∫ t, Fejer.kernel N t • T t v ∂AddCircle.haarAddCircle := by
  have hint (r : ℤ) : Integrable (fun t : Fejer.Circle => fourier r t • T t v)
      AddCircle.haarAddCircle :=
    ((fourier r).continuous.smul (hT v)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  calc
    average C N v = ∑ r ∈ Fejer.frequencies N,
        Fejer.coefficient N r • ∫ t, fourier r t • T t v ∂AddCircle.haarAddCircle := by
      simp only [average, sum_apply, smul_apply, hC]
    _ = ∫ t, ∑ r ∈ Fejer.frequencies N,
        Fejer.coefficient N r • (fourier r t • T t v) ∂AddCircle.haarAddCircle := by
      rw [integral_finsetSum]
      · simp only [integral_smul]
      · intro r hr
        exact (hint r).smul _
    _ = ∫ t, Fejer.kernel N t • T t v ∂AddCircle.haarAddCircle := by
      apply integral_congr_ae
      exact Eventually.of_forall fun t => by
        change (∑ r ∈ Fejer.frequencies N, Fejer.coefficient N r • (fourier r t • T t v)) =
          Fejer.kernel N t • T t v
        rw [← Complex.coe_smul, Fejer.kernel_eq_finite_fourier_sum, Finset.sum_smul]
        simp only [mul_smul]

theorem average_tendsto
    (T : Fejer.Circle → H →L[ℂ] H)
    (hT : ∀ v : H, Continuous (fun t => T t v))
    (C : ℤ → H →L[ℂ] H)
    (hC : ∀ r v, C r v = ∫ t, fourier r t • T t v ∂AddCircle.haarAddCircle)
    (v : H) :
    Tendsto (fun n : ℕ => average C (n + 1) v) atTop (𝓝 (T 0 v)) := by
  simpa only [average_apply T hT C hC] using
    Fejer.tendsto_integral_kernel_smul_of_continuous (hT v)

theorem mem_of_fourier_modes
    (M : VonNeumannAlgebra H) (T : Fejer.Circle → H →L[ℂ] H)
    (hT : ∀ v : H, Continuous (fun t => T t v))
    (C : ℤ → H →L[ℂ] H)
    (hC : ∀ r v, C r v = ∫ t, fourier r t • T t v ∂AddCircle.haarAddCircle)
    (hCm : ∀ r, C r ∈ M) : T 0 ∈ M := by
  apply vonNeumannAlgebra_mem_of_strong_tendsto M
    (l := atTop) (A := fun n : ℕ => average C (n + 1))
  · intro n
    apply M.toStarSubalgebra.sum_mem
    intro r hr
    exact M.toStarSubalgebra.smul_mem (hCm r) _
  · exact average_tendsto T hT C hC

end StrongFourierRecovery
end Invariant233

end

end OAI
