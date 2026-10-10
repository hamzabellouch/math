import OAI.Analysis.IrrationalRotation.Analysis.ScalarMultiplierFields

namespace OAI

namespace Invariant233.DirectIntegral

open MeasureTheory Filter
open scoped ENNReal

variable {X E ι : Type*} [MeasurableSpace X] {μ : Measure X}
  [IsFiniteMeasure μ] [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [Countable ι]

omit [IsFiniteMeasure μ] in
theorem represented_mul
    (T U : Lp E 2 μ →L[ℂ] Lp E 2 μ) (A B : X → E →L[ℂ] E)
    (hT : ∀ f : Lp E 2 μ, T f =ᵐ[μ] fun x => A x (f x))
    (hU : ∀ f : Lp E 2 μ, U f =ᵐ[μ] fun x => B x (f x))
    (f : Lp E 2 μ) :
    (T * U) f =ᵐ[μ] fun x => (A x * B x) (f x) := by
  filter_upwards [hT (U f), hU f] with x hx hy
  change T (U f) x = A x (B x (f x))
  rw [hx, hy]

theorem ae_commute_of_represented_commute
    (b : HilbertBasis ι ℂ E)
    (T U : Lp E 2 μ →L[ℂ] Lp E 2 μ) (A B : X → E →L[ℂ] E)
    (hT : ∀ f : Lp E 2 μ, T f =ᵐ[μ] fun x => A x (f x))
    (hU : ∀ f : Lp E 2 μ, U f =ᵐ[μ] fun x => B x (f x))
    (hcomm : Commute T U) : ∀ᵐ x ∂μ, Commute (A x) (B x) := by
  have hAB : (fun x => A x * B x) =ᵐ[μ] (fun x => B x * A x) := by
    apply L2Multiplication.field_unique_of_representation b (T * U)
    · exact represented_mul T U A B hT hU
    · rw [hcomm.eq]
      exact represented_mul U T B A hU hT
  filter_upwards [hAB] with x hx
  exact hx

end Invariant233.DirectIntegral

end OAI
