import OAI.Analysis.IrrationalRotation.Analysis.ScalarMultiplierFields
import OAI.Analysis.IrrationalRotation.Analysis.FieldKoopman

namespace OAI

noncomputable section
open MeasureTheory Filter

namespace Invariant233.DirectIntegral

variable {X E ι : Type*} [MeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [Countable ι]

theorem ae_commute_of_representations (b : HilbertBasis ι ℂ E)
    (T B : Lp E 2 μ →L[ℂ] Lp E 2 μ) (F G : X → E →L[ℂ] E)
    (hT : ∀ ξ : Lp E 2 μ, T ξ =ᵐ[μ] fun x => F x (ξ x))
    (hB : ∀ ξ : Lp E 2 μ, B ξ =ᵐ[μ] fun x => G x (ξ x))
    (hcomm : Commute T B) : ∀ᵐ x ∂μ, Commute (F x) (G x) := by
  apply L2Multiplication.field_unique_of_representation b (T * B)
    (fun x => F x * G x) (fun x => G x * F x)
  · intro ξ
    filter_upwards [hT (B ξ), hB ξ] with x hx hy
    change T (B ξ) x = F x (G x (ξ x))
    rw [hx, hy]
  · intro ξ
    rw [hcomm.eq]
    filter_upwards [hB (T ξ), hT ξ] with x hx hy
    change B (T ξ) x = G x (F x (ξ x))
    rw [hx, hy]

theorem ae_covariance_of_represented_commute (b : HilbertBasis ι ℂ E)
    (T : Lp E 2 μ →L[ℂ] Lp E 2 μ) (F : X → E →L[ℂ] E)
    (S : E →L[ℂ] E) (σ : X → X) (hσ : MeasurePreserving σ μ μ)
    (hT : ∀ ξ : Lp E 2 μ, T ξ =ᵐ[μ] fun x => F x (ξ x))
    (hcomm : Commute T (shiftedPullback S σ hσ)) :
    ∀ᵐ x ∂μ, F x * S = S * F (σ x) := by
  apply Fields.ae_eq_of_countable_columns
    (Submodule.dense_iff_topologicalClosure_eq_top.mpr b.dense_span)
  intro i
  let ξ : Lp E 2 μ := Lp.const 2 μ (b i)
  let J := shiftedPullback S σ hσ
  have heq : T (J ξ) = J (T ξ) :=
    congrArg (fun A : Lp E 2 μ →L[ℂ] Lp E 2 μ => A ξ) hcomm.eq
  filter_upwards [hT (J ξ), FieldKoopman.operator_ae S σ hσ ξ,
    FieldKoopman.operator_ae S σ hσ (T ξ),
    hσ.quasiMeasurePreserving.ae (hT ξ),
    hσ.quasiMeasurePreserving.ae (Lp.coeFn_const 2 μ (b i))]
    with x hTJ hJ hJT hTσ hξ
  have hx := congrArg (fun η : Lp E 2 μ => η x) heq
  change ξ (σ x) = b i at hξ
  change T (J ξ) x = J (T ξ) x at hx
  rw [hTJ, hJ, hJT, hTσ, hξ] at hx
  exact hx

end Invariant233.DirectIntegral

end

end OAI
