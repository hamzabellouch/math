import OAI.Analysis.IrrationalRotation.Model.ShiftedPullback
import Mathlib

namespace OAI

noncomputable section
open MeasureTheory Filter
open scoped Topology

namespace Invariant233.FieldKoopman

variable {X E : Type*} [MeasurableSpace X]
  [NormedAddCommGroup E] [NormedSpace ℂ E] {μ : Measure X}

open DirectIntegral

theorem operator_ae (S : E →L[ℂ] E) (σ : X → X) (hσ : MeasurePreserving σ μ μ)
    (ξ : Lp E 2 μ) :
    shiftedPullback S σ hσ ξ =ᵐ[μ] fun x => S (ξ (σ x)) := by
  filter_upwards [S.coeFn_compLpL (Lp.compMeasurePreserving σ hσ ξ),
    Lp.coeFn_compMeasurePreserving ξ hσ] with x hx hy
  exact hx.trans (congrArg S hy)

theorem operator_mul (S R : E →L[ℂ] E) (σ τ : X → X)
    (hσ : MeasurePreserving σ μ μ) (hτ : MeasurePreserving τ μ μ) :
    shiftedPullback S σ hσ * shiftedPullback R τ hτ =
      shiftedPullback (S * R) (τ ∘ σ) (hτ.comp hσ) := by
  apply ContinuousLinearMap.ext
  intro ξ
  apply Lp.ext
  filter_upwards [operator_ae S σ hσ (shiftedPullback R τ hτ ξ),
    hσ.quasiMeasurePreserving.ae (operator_ae R τ hτ ξ),
    operator_ae (S * R) (τ ∘ σ) (hτ.comp hσ) ξ] with x hx hy hz
  change shiftedPullback S σ hσ (shiftedPullback R τ hτ ξ) x = _
  rw [hx, hy, hz]
  rfl

theorem operator_one_id :
    shiftedPullback (1 : E →L[ℂ] E) id (MeasurePreserving.id μ) = 1 := by
  apply ContinuousLinearMap.ext
  intro ξ
  apply Lp.ext
  filter_upwards [operator_ae (1 : E →L[ℂ] E) id (MeasurePreserving.id μ) ξ] with x hx
  exact hx

theorem operator_mul_eq_one (S R : E →L[ℂ] E) (σ τ : X → X)
    (hσ : MeasurePreserving σ μ μ) (hτ : MeasurePreserving τ μ μ)
    (hSR : S * R = 1) (hτσ : τ ∘ σ = id) :
    shiftedPullback S σ hσ * shiftedPullback R τ hτ = 1 := by
  rw [operator_mul, hSR]
  simpa only [hτσ] using (operator_one_id (E := E) (μ := μ))

theorem commute_of_represented_covariance
    (T : Lp E 2 μ →L[ℂ] Lp E 2 μ) (A : X → E →L[ℂ] E)
    (hT : ∀ ξ : Lp E 2 μ, ∀ᵐ x ∂μ, (T ξ) x = A x (ξ x))
    (S : E →L[ℂ] E) (σ : X → X) (hσ : MeasurePreserving σ μ μ)
    (hcov : ∀ᵐ x ∂μ, A x * S = S * A (σ x)) :
    Commute T (shiftedPullback S σ hσ) := by
  apply ContinuousLinearMap.ext
  intro ξ
  apply Lp.ext
  filter_upwards [hT (shiftedPullback S σ hσ ξ), operator_ae S σ hσ ξ,
    operator_ae S σ hσ (T ξ), hσ.quasiMeasurePreserving.ae (hT ξ), hcov]
    with x hTx hJx hJTx hTσx hcovx
  change T (shiftedPullback S σ hσ ξ) x = shiftedPullback S σ hσ (T ξ) x
  rw [hTx, hJx, hJTx, hTσx]
  exact congrArg (fun B : E →L[ℂ] E => B (ξ (σ x))) hcovx

theorem commute_const (R S : E →L[ℂ] E) (σ : X → X)
    (hσ : MeasurePreserving σ μ μ) (hRS : Commute R S) :
    Commute (R.compLpL 2 μ) (shiftedPullback S σ hσ) := by
  apply commute_of_represented_covariance (R.compLpL 2 μ) (fun _ => R)
    (fun ξ => R.coeFn_compLpL ξ) S σ hσ
  exact Filter.Eventually.of_forall (fun _ => hRS.eq)

theorem norm_operator (S : E ≃ₗᵢ[ℂ] E) (σ : X → X)
    (hσ : MeasurePreserving σ μ μ) (ξ : Lp E 2 μ) :
    ‖shiftedPullback S.toLinearIsometry.toContinuousLinearMap σ hσ ξ‖ = ‖ξ‖ := by
  rw [Lp.norm_def, Lp.norm_def]
  congr 1
  calc
    eLpNorm (shiftedPullback S.toLinearIsometry.toContinuousLinearMap σ hσ ξ) 2 μ =
        eLpNorm (fun x => ξ (σ x)) 2 μ := by
      apply eLpNorm_congr_norm_ae (Lp.aestronglyMeasurable _)
        ((Lp.aestronglyMeasurable ξ).comp_measurePreserving hσ)
      filter_upwards [operator_ae S.toLinearIsometry.toContinuousLinearMap σ hσ ξ]
        with x hx
      rw [hx]
      exact S.norm_map _
    _ = eLpNorm ξ 2 μ :=
      eLpNorm_comp_measurePreserving (Lp.aestronglyMeasurable ξ) hσ

def equivalence (S : E ≃ₗᵢ[ℂ] E) (σ τ : X → X)
    (hσ : MeasurePreserving σ μ μ) (hτ : MeasurePreserving τ μ μ)
    (hτσ : τ ∘ σ = id) (hστ : σ ∘ τ = id) :
    Lp E 2 μ ≃ₗᵢ[ℂ] Lp E 2 μ where
  toFun := shiftedPullback S.toLinearIsometry.toContinuousLinearMap σ hσ
  invFun := shiftedPullback S.symm.toLinearIsometry.toContinuousLinearMap τ hτ
  map_add' := map_add _
  map_smul' := map_smul _
  left_inv ξ := by
    have h := operator_mul_eq_one S.symm.toLinearIsometry.toContinuousLinearMap
      S.toLinearIsometry.toContinuousLinearMap τ σ hτ hσ
      (by ext v; exact S.symm_apply_apply v) hστ
    exact congrArg (fun T : Lp E 2 μ →L[ℂ] Lp E 2 μ => T ξ) h
  right_inv ξ := by
    have h := operator_mul_eq_one S.toLinearIsometry.toContinuousLinearMap
      S.symm.toLinearIsometry.toContinuousLinearMap σ τ hσ hτ
      (by ext v; exact S.apply_symm_apply v) hτσ
    exact congrArg (fun T : Lp E 2 μ →L[ℂ] Lp E 2 μ => T ξ) h
  norm_map' := norm_operator S σ hσ

theorem operator_mem_unitary
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    (S : F ≃ₗᵢ[ℂ] F) (σ τ : X → X)
    (hσ : MeasurePreserving σ μ μ) (hτ : MeasurePreserving τ μ μ)
    (hτσ : τ ∘ σ = id) (hστ : σ ∘ τ = id) :
    shiftedPullback S.toLinearIsometry.toContinuousLinearMap σ hσ ∈
      unitary (Lp F 2 μ →L[ℂ] Lp F 2 μ) := by
  exact (Unitary.linearIsometryEquiv.symm (equivalence S σ τ hσ hτ hτσ hστ)).property

end Invariant233.FieldKoopman

end

end OAI
