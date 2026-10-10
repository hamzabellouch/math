import OAI.Analysis.LipschitzHilbert.Estimates.CountingDiscard

namespace OAI

/-! The fixed concentration/count exception is charged to the original
L2 packet sum with the prescribed polynomial area budget. -/

noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace LipschitzHilbert
variable {X E : Type*} [MeasurableSpace X] [NormedAddCommGroup E]

theorem original_fixed_exception_cost (μ : Measure X) (P : X → E)
    (hP : MemLp P 2 μ) (bad testing : Set X) (hbad : μ bad ≠ ∞)
    (L q Q N : ℝ) (hL : 0 < L) (hN : 0 ≤ N)
    (hmodel : (∫ x, ‖P x‖^2 ∂μ) ≤ (L^q)^2*(N^2*μ.real testing))
    (harea : μ.real bad ≤ (L^(-q-Q))^2*μ.real testing) :
    IntegrableOn (fun x => ‖P x‖) bad μ ∧
      (∫ x in bad, ‖P x‖ ∂μ) ≤ L^(-Q)*N*μ.real testing := by
  obtain ⟨hi,hcs⟩ := integral_norm_on_set_le_l2 μ P hP hbad
  refine ⟨hi,hcs.trans ?_⟩
  calc
    _ ≤ Real.sqrt ((L^q)^2*(N^2*μ.real testing))*
        Real.sqrt ((L^(-q-Q))^2*μ.real testing) :=
      mul_le_mul (Real.sqrt_le_sqrt hmodel) (Real.sqrt_le_sqrt harea)
        (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    _ = L^(-Q)*N*μ.real testing := by
      rw [Real.sqrt_mul (sq_nonneg _),Real.sqrt_sq (Real.rpow_nonneg hL.le _),
        Real.sqrt_mul (sq_nonneg N),Real.sqrt_sq hN,
        Real.sqrt_mul (sq_nonneg _),Real.sqrt_sq (Real.rpow_nonneg hL.le _)]
      have hpow : L^q*L^(-q-Q) = L^(-Q) := by
        rw [←Real.rpow_add hL]
        congr 1
        ring
      calc
        _ = (L^q*L^(-q-Q))*N*(Real.sqrt (μ.real testing)*Real.sqrt (μ.real testing)) := by ring
        _ = _ := by rw [hpow,Real.mul_self_sqrt measureReal_nonneg]

end LipschitzHilbert

end

end OAI
