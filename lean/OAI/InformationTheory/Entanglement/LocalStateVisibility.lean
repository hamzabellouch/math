import OAI.InformationTheory.Entanglement.CausalRealization
import OAI.InformationTheory.Entanglement.TraceInstrument

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Function
namespace SecretKey
variable {X S : Type*}
variable (role : ℕ → TapeRole) (pub : Set ℕ) (x₀ : X) (r : TapeRole)
variable [MeasurableSpace X] [StandardBorelSpace X] [Nonempty X]
variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
variable {ι κ : Type*} (b : HilbertBasis ι ℂ H) (d : HilbertBasis κ ℂ K)

omit [StandardBorelSpace X] [Nonempty X] [CompleteSpace H] in
theorem local_born_kernel_visible
    (s₀ : DensityOperator b)
    (U : (n : ℕ) → (Fin n → X) → DensityOperator b → X → DensityOperator b)
    (n : ℕ) (J : (Fin n → X) → TraceInstrument b d X)
    (hm : ∀ A, MeasurableSet A → Measurable (fun h =>
      (J (visiblePrefix role pub x₀ r n h)).outcome (localStateAt role pub x₀ r s₀ U n h) A)) :
    TraceInstrument.historyKernel
      (fun h => J (visiblePrefix role pub x₀ r n h)) (localStateAt role pub x₀ r s₀ U n) hm=
    (TraceInstrument.historyKernel
      (fun h => J (visiblePrefix role pub x₀ r n h)) (localStateAt role pub x₀ r s₀ U n) hm).comap
        (visiblePrefix role pub x₀ r n) (visiblePrefix_measurable role pub x₀ r n) := by

  let : MeasurableSpace (DensityOperator b) := ⊤
  ext h A hA
  simp only [Kernel.comap_apply,TraceInstrument.historyKernel,Kernel.coe_mk,
    visiblePrefix_idem,localStateAt_visible]

end SecretKey

end

end OAI
