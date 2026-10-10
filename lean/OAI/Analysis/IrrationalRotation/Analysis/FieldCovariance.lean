import OAI.Analysis.IrrationalRotation.Analysis.FieldVectorState
import OAI.Analysis.IrrationalRotation.Operators.HilbertModelSize
import OAI.Analysis.IrrationalRotation.Model.ShiftedPullback

namespace OAI

open MeasureTheory Filter
open scoped InnerProductSpace Topology

namespace Invariant233.FieldTraceCyclic

variable {Ω E : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  {μ : Measure Ω} [IsFiniteMeasure μ]

omit [IsFiniteMeasure μ] in

theorem shiftedPullback_ae (S : E →L[ℂ] E) (σ : Ω → Ω)
    (hσ : MeasurePreserving σ μ μ) (ξ : Lp E 2 μ) :
    ∀ᵐ x ∂μ, (DirectIntegral.shiftedPullback S σ hσ ξ) x = S (ξ (σ x)) := by
  filter_upwards [S.coeFn_compLpL (Lp.compMeasurePreserving σ hσ ξ),
    Lp.coeFn_compMeasurePreserving ξ hσ] with x hSx hσx
  exact hSx.trans (congrArg S hσx)

theorem ae_covariance_apply_of_commute
    (T J : Lp E 2 μ →L[ℂ] Lp E 2 μ) (A : Ω → E →L[ℂ] E)
    (S : E →L[ℂ] E) (σ : Ω → Ω) (hσ : MeasurePreserving σ μ μ)
    (hT : ∀ ξ : Lp E 2 μ, ∀ᵐ x ∂μ, (T ξ) x = A x (ξ x))
    (hJ : ∀ ξ : Lp E 2 μ, ∀ᵐ x ∂μ, (J ξ) x = S (ξ (σ x)))
    (hcomm : Commute T J) (v : E) :
    ∀ᵐ x ∂μ, A x (S v) = S (A (σ x) v) := by
  let c := Lp.const 2 μ v
  have hc : ∀ᵐ x ∂μ, c (σ x) = v :=
    hσ.quasiMeasurePreserving.ae (Lp.coeFn_const 2 μ v)
  have hTc : ∀ᵐ x ∂μ, (T c) (σ x) = A (σ x) (c (σ x)) :=
    hσ.quasiMeasurePreserving.ae (hT c)
  have heq : T (J c) = J (T c) :=
    congrArg (fun R : Lp E 2 μ →L[ℂ] Lp E 2 μ => R c) hcomm.eq
  filter_upwards [hT (J c), hJ c, hJ (T c), hc, hTc] with x hTx hJx hJTx hcx hTcx
  have heqx := congrArg (fun ξ : Lp E 2 μ => ξ x) heq
  rw [hTx, hJx, hJTx, hTcx, hcx] at heqx
  exact heqx

theorem ae_covariance_of_commute [TopologicalSpace.SeparableSpace E]
    (T J : Lp E 2 μ →L[ℂ] Lp E 2 μ) (A : Ω → E →L[ℂ] E)
    (S : E →L[ℂ] E) (σ : Ω → Ω) (hσ : MeasurePreserving σ μ μ)
    (hT : ∀ ξ : Lp E 2 μ, ∀ᵐ x ∂μ, (T ξ) x = A x (ξ x))
    (hJ : ∀ ξ : Lp E 2 μ, ∀ᵐ x ∂μ, (J ξ) x = S (ξ (σ x)))
    (hcomm : Commute T J) :
    ∀ᵐ x ∂μ, A x * S = S * A (σ x) := by
  let v := TopologicalSpace.denseSeq E
  have hv : DenseRange v := TopologicalSpace.denseRange_denseSeq E
  have hall : ∀ᵐ x ∂μ, ∀ n : ℕ, A x (S (v n)) = S (A (σ x) (v n)) :=
    ae_all_iff.mpr (fun n => ae_covariance_apply_of_commute T J A S σ hσ hT hJ hcomm (v n))
  filter_upwards [hall] with x hx
  apply ContinuousLinearMap.ext
  intro w
  exact hv.induction_on w
    (isClosed_eq ((A x).continuous.comp S.continuous)
      (S.continuous.comp (A (σ x)).continuous)) hx

theorem ae_matrix_covariance_of_commute
    (b : HilbertBasis ℤ ℂ E)
    (T : Lp E 2 μ →L[ℂ] Lp E 2 μ) (A : Ω → E →L[ℂ] E)
    (J : ℤ → Lp E 2 μ →L[ℂ] Lp E 2 μ)
    (S : ℤ → E →ₗᵢ[ℂ] E) (σ : ℤ → Ω → Ω)
    (hσ : ∀ r, MeasurePreserving (σ r) μ μ)
    (hS : ∀ r k : ℤ, S r (b k) = b (k + r))
    (hT : ∀ ξ : Lp E 2 μ, ∀ᵐ x ∂μ, (T ξ) x = A x (ξ x))
    (hJ : ∀ r (ξ : Lp E 2 μ), ∀ᵐ x ∂μ, (J r ξ) x = S r (ξ (σ r x)))
    (hcomm : ∀ r, Commute T (J r)) :
    ∀ r k l : ℤ, ∀ᵐ x ∂μ,
      inner ℂ (b k) (A (σ r x) (b l)) =
        inner ℂ (b (k + r)) (A x (b (l + r))) := by
  intro r k l
  have hv := ae_covariance_apply_of_commute T (J r) A (S r).toContinuousLinearMap
    (σ r) (hσ r) hT (hJ r) (hcomm r) (b l)
  filter_upwards [hv] with x hx
  change A x (S r (b l)) = S r (A (σ r x) (b l)) at hx
  calc
    inner ℂ (b k) (A (σ r x) (b l)) =
        inner ℂ (S r (b k)) (S r (A (σ r x) (b l))) :=
      ((S r).inner_map_map (b k) (A (σ r x) (b l))).symm
    _ = inner ℂ (b (k + r)) (A x (b (l + r))) := by
      rw [hS, ← hx, hS]

omit [IsFiniteMeasure μ] in

theorem commute_shiftedPullback_of_covariance
    (T : Lp E 2 μ →L[ℂ] Lp E 2 μ) (A : Ω → E →L[ℂ] E)
    (S : E →L[ℂ] E) (σ : Ω → Ω) (hσ : MeasurePreserving σ μ μ)
    (hT : ∀ ξ : Lp E 2 μ, ∀ᵐ x ∂μ, (T ξ) x = A x (ξ x))
    (hcov : ∀ᵐ x ∂μ, A x * S = S * A (σ x)) :
    Commute T (DirectIntegral.shiftedPullback S σ hσ) := by
  change T * DirectIntegral.shiftedPullback S σ hσ =
    DirectIntegral.shiftedPullback S σ hσ * T
  apply ContinuousLinearMap.ext
  intro ξ
  apply Lp.ext
  filter_upwards [hT (DirectIntegral.shiftedPullback S σ hσ ξ),
    shiftedPullback_ae S σ hσ ξ, shiftedPullback_ae S σ hσ (T ξ),
    hσ.quasiMeasurePreserving.ae (hT ξ), hcov] with x hTx hJx hJTx hTσx hcovx
  change (T (DirectIntegral.shiftedPullback S σ hσ ξ)) x =
    (DirectIntegral.shiftedPullback S σ hσ (T ξ)) x
  rw [hTx, hJx, hJTx, hTσx]
  exact congrArg (fun R : E →L[ℂ] E => R (ξ (σ x))) hcovx

theorem commute_shiftedPullback_iff_covariance [TopologicalSpace.SeparableSpace E]
    (T : Lp E 2 μ →L[ℂ] Lp E 2 μ) (A : Ω → E →L[ℂ] E)
    (S : E →L[ℂ] E) (σ : Ω → Ω) (hσ : MeasurePreserving σ μ μ)
    (hT : ∀ ξ : Lp E 2 μ, ∀ᵐ x ∂μ, (T ξ) x = A x (ξ x)) :
    Commute T (DirectIntegral.shiftedPullback S σ hσ) ↔
      ∀ᵐ x ∂μ, A x * S = S * A (σ x) := by
  exact ⟨ae_covariance_of_commute T _ A S σ hσ hT (shiftedPullback_ae S σ hσ),
    commute_shiftedPullback_of_covariance T A S σ hσ hT⟩

end Invariant233.FieldTraceCyclic

end OAI
