import OAI.Probability.SLE.Mass.RadonProcessUniqueness
import OAI.Probability.SLE.Mass.RationalTraceMassLocalVariation
import OAI.Probability.SLE.Mass.LocallyFiniteMeasureSubtract

namespace OAI

/-! Local exhaustion determines the terminal measure once the finite-time
increasing Radon family is fixed. -/

noncomputable section
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

namespace SLEExactGauge

lemma radon_terminal_eq_of_common_exhaustion
    {X : Type*} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
    [MeasurableSpace X] [BorelSpace X]
    (μ ν : Measure X) [μ.Regular] [ν.Regular]
    (N : ℝ≥0 → Measure X)
    (hμ : ∀ t, N t ≤ μ) (hν : ∀ t, N t ≤ ν)
    (hlμ : ∀ K : Set X, IsCompact K → Tendsto (fun t : ℝ≥0 => (μ-N t) K) atTop (𝓝 0))
    (hlν : ∀ K : Set X, IsCompact K → Tendsto (fun t : ℝ≥0 => (ν-N t) K) atTop (𝓝 0)) :
    μ = ν := by
  have hle (ρ σ : Measure X) [ρ.Regular] (hρ : ∀ t, N t ≤ ρ) (hσ : ∀ t, N t ≤ σ)
      (hl : ∀ K : Set X, IsCompact K → Tendsto (fun t : ℝ≥0 => (ρ-N t) K) atTop (𝓝 0))
      (K : Set X) (hK : IsCompact K) : ρ K ≤ σ K := by
    have hb (t : ℝ≥0) : ρ K ≤ σ K+(ρ-N t) K := by
      let : IsFiniteMeasureOnCompacts (N t) :=
        ⟨fun L hL => lt_of_le_of_lt (hρ t L) hL.measure_lt_top⟩
      rw [sub_apply_of_finite_restriction (hρ t) hK.measurableSet hK.measure_lt_top.ne]
      calc
        ρ K = (ρ K-N t K)+N t K := (tsub_add_cancel_of_le (hρ t K)).symm
        _ ≤ (ρ K-N t K)+σ K := add_le_add le_rfl (hσ t K)
        _ = _ := add_comm _ _
    have hlim := (tendsto_const_nhds (x := σ K)).add (hl K hK)
    simp only [add_zero] at hlim
    exact le_of_tendsto_of_tendsto' tendsto_const_nhds hlim hb
  apply Measure.OuterRegular.ext_isOpen
  apply Measure.InnerRegularWRT.eq_of_innerRegularWRT_of_forall_eq
    Measure.Regular.innerRegular Measure.Regular.innerRegular
  intro K hK
  exact (hle μ ν hμ hν hlμ K hK).antisymm (hle ν μ hν hμ hlν K hK)

end SLEExactGauge

end

end OAI
