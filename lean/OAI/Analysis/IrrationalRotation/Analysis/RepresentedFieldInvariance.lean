import OAI.Analysis.IrrationalRotation.Analysis.ScalarMultiplierFields

namespace OAI

noncomputable section
open MeasureTheory Filter
namespace Invariant233.DirectIntegral

variable {X E ι : Type*} [MeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [Countable ι]

theorem ae_invariant_of_representations (b : HilbertBasis ι ℂ E)
    (P T : Lp E 2 μ →L[ℂ] Lp E 2 μ) (F G : X → E →L[ℂ] E)
    (hP : ∀ ξ : Lp E 2 μ, P ξ =ᵐ[μ] fun x => F x (ξ x))
    (hT : ∀ ξ : Lp E 2 μ, T ξ =ᵐ[μ] fun x => G x (ξ x))
    (hinv : (1 - P) * T * P = 0) :
    ∀ᵐ x ∂μ, (1 - F x) * G x * F x = 0 := by
  apply Fields.ae_eq_of_countable_columns
    (Submodule.dense_iff_topologicalClosure_eq_top.mpr b.dense_span)
  intro i
  let ξ : Lp E 2 μ := Lp.const 2 μ (b i)
  have heq : T (P ξ) = P (T (P ξ)) := by
    have h := congrArg (fun A : Lp E 2 μ →L[ℂ] Lp E 2 μ => A ξ) hinv
    change T (P ξ) - P (T (P ξ)) = 0 at h
    exact sub_eq_zero.mp h
  filter_upwards [hP ξ, hT (P ξ), hP (T (P ξ)), Lp.coeFn_const 2 μ (b i)]
    with x hPx hTx hPTx hξ
  have hx := congrArg (fun η : Lp E 2 μ => η x) heq
  change ξ x = b i at hξ
  rw [hTx, hPTx, hTx, hPx, hξ] at hx
  change G x (F x (b i)) - F x (G x (F x (b i))) = 0
  exact sub_eq_zero.mpr hx

end Invariant233.DirectIntegral

end

end OAI
