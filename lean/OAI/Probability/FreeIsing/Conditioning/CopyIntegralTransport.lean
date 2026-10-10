import OAI.Probability.FreeIsing.Brownian.IntegralTransport
import OAI.Probability.FreeIsing.Conditioning.Copies

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Filter TopologicalSpace
open scoped Topology

namespace Problem367.ConditionalIntegralTransport

variable {W Ω : Type*}

def pair (j : Bool) (q : W × (Ω × Ω)) : W × Ω :=
  (q.1, if j then q.2.1 else q.2.2)

theorem pair_measurePreserving [MeasurableSpace W] [MeasurableSpace Ω]
    (ρ : Measure W) [SFinite ρ] (κ : Kernel W Ω) [IsMarkovKernel κ] (j : Bool) :
    MeasurePreserving (pair (W := W) (Ω := Ω) j) (ρ ⊗ₘ (κ ×ₖ κ)) (ρ ⊗ₘ κ) := by
  cases j
  · exact measurePreserving_conditionalCopy_snd ρ κ
  · exact measurePreserving_conditionalCopy_fst ρ κ

theorem integral_transport
    {V T : Type*} [MeasurableSpace W] [MeasurableSpace Ω] [Countable V]
    [TopologicalSpace T] [SeparableSpace T] [Nonempty T]
    (ρ : Measure W) [SFinite ρ] (κ : Kernel W Ω) [IsMarkovKernel κ]
    {X : V → T → ℕ → W × Ω → ℝ} {I : V → T → W × Ω → ℝ}
    {J : Bool → V → T → W × (Ω × Ω) → ℝ}
    (hX : ∀ v t n, MemLp (X v t n) 2 (ρ ⊗ₘ κ))
    (hI : ∀ v t, MemLp (I v t) 2 (ρ ⊗ₘ κ))
    (hJ : ∀ j v t, MemLp (J j v t) 2 (ρ ⊗ₘ (κ ×ₖ κ)))
    (hcI : ∀ v, ∀ᵐ q ∂ρ ⊗ₘ κ, Continuous (fun t => I v t q))
    (hcJ : ∀ j v, ∀ᵐ q ∂ρ ⊗ₘ (κ ×ₖ κ), Continuous (fun t => J j v t q))
    (hlimI : ∀ v t, Tendsto (fun n => ∫ q, (X v t n q - I v t q) ^ 2 ∂ρ ⊗ₘ κ)
      atTop (𝓝 0))
    (hlimJ : ∀ j v t, Tendsto (fun n => ∫ q,
      (X v t n (pair j q) - J j v t q) ^ 2 ∂ρ ⊗ₘ (κ ×ₖ κ)) atTop (𝓝 0)) :
    ∀ᵐ q ∂ρ ⊗ₘ (κ ×ₖ κ), ∀ j v t, I v t (pair j q) = J j v t q := by
  have hj : ∀ j, (fun q v t => I v t (pair j q)) =ᵐ[ρ ⊗ₘ (κ ×ₖ κ)]
      (fun q v t => J j v t q) := fun j =>
    BrownianGrid.ae_eq_array_of_meanSquare_limits_comp (pair_measurePreserving ρ κ j)
      hX hI (hJ j) hcI (hcJ j) hlimI (hlimJ j)
  filter_upwards [ae_all_iff.mpr hj] with q hq
  intro j v t
  exact congrFun (congrFun (hq j) v) t

end Problem367.ConditionalIntegralTransport

end

end OAI
