import OAI.Analysis.KadisonSimilarity.FreeProduct.DihedralContinuousMoments
import OAI.Analysis.KadisonSimilarity.FreeProduct.AngularIntegralBounds

namespace OAI

/-! The Haar law determines the continuous functional calculus of the real
part of the rotation, tested against every rotation power. -/

noncomputable section
namespace KadisonSimilarity

variable {A : Type*} [CStarAlgebra A]

theorem trace_cfc_realPart_rotation (τ : A →L[ℂ] ℂ) (w : Aˣ)
    (hw : star (w : A) = (↑w⁻¹ : A)) (hwn : ‖(w : A)‖ ≤ 1)
    (hhaar : ∀ l : ℤ, τ (↑(w ^ l) : A) = if l = 0 then 1 else 0)
    (f : ℝ → ℝ) (hf : Continuous f) (l : ℤ) :
    τ (cfc f (realPart (w : A) : A) * (↑(w ^ l) : A)) =
      angularIntegral (fun x => (f (Real.cos x) : ℂ)) l := by
  let a : A := realPart (w : A)
  let b : A := (↑(w ^ l) : A)
  have han : ‖a‖ ≤ 1 := (realPart.norm_le (w : A)).trans hwn
  apply sub_eq_zero.mp
  apply norm_eq_zero.mp
  apply le_antisymm _ (norm_nonneg _)
  apply le_of_forall_pos_le_add
  intro ε hε
  let K : ℝ := ‖τ‖ * ‖b‖ + 1
  have hK : 0 < K := by dsimp [K]; positivity
  let δ := ε / K
  have hδ : 0 < δ := div_pos hε hK
  obtain ⟨p, hp, hpOn⟩ := exists_polynomial_near_cfc a
    (realPart (w : A)).property han f hf.continuousOn hδ
  have hpoly : τ (Polynomial.aeval a p * b) =
      angularIntegral (fun x => ((p.eval (Real.cos x) : ℝ) : ℂ)) l := by
    simpa only [a, b, angularIntegral, ContinuousLinearMap.coe_coe] using
      trace_realPart_polynomial_rotation τ.toLinearMap w hw hhaar p l
  have heq : τ (cfc f a * b) - τ (Polynomial.aeval a p * b) =
      τ ((cfc f a - Polynomial.aeval a p) * b) := by rw [sub_mul, map_sub]
  have hop : ‖τ (cfc f a * b) - τ (Polynomial.aeval a p * b)‖ ≤
      ‖τ‖ * (δ * ‖b‖) := by
    rw [heq]
    calc
      _ ≤ ‖τ‖ * ‖(cfc f a - Polynomial.aeval a p) * b‖ := τ.le_opNorm _
      _ ≤ ‖τ‖ * (‖cfc f a - Polynomial.aeval a p‖ * ‖b‖) :=
        mul_le_mul_of_nonneg_left (norm_mul_le _ _) (norm_nonneg _)
      _ ≤ ‖τ‖ * (δ * ‖b‖) := by gcongr
  have hint : ‖angularIntegral (fun x => ((p.eval (Real.cos x) : ℝ) : ℂ)) l -
      angularIntegral (fun x => (f (Real.cos x) : ℂ)) l‖ ≤ δ := by
    apply angularIntegral_continuous_sub_bound _ _
      (Complex.continuous_ofReal.comp (p.continuous.comp Real.continuous_cos))
      (Complex.continuous_ofReal.comp (hf.comp Real.continuous_cos)) l hδ.le
    intro x _
    have h := (hpOn (Real.cos x) ⟨Real.neg_one_le_cos x, Real.cos_le_one x⟩).le
    simpa only [Function.comp_apply, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] using h
  change ‖τ (cfc f a * b) - angularIntegral (fun x => (f (Real.cos x) : ℂ)) l‖ ≤ 0 + ε
  rw [zero_add]
  calc
    _ = ‖(τ (cfc f a * b) - τ (Polynomial.aeval a p * b)) +
        (angularIntegral (fun x => ((p.eval (Real.cos x) : ℝ) : ℂ)) l -
          angularIntegral (fun x => (f (Real.cos x) : ℂ)) l)‖ := by rw [hpoly]; congr 1; ring
    _ ≤ ‖τ (cfc f a * b) - τ (Polynomial.aeval a p * b)‖ +
        ‖angularIntegral (fun x => ((p.eval (Real.cos x) : ℝ) : ℂ)) l -
          angularIntegral (fun x => (f (Real.cos x) : ℂ)) l‖ := norm_add_le _ _
    _ ≤ ‖τ‖ * (δ * ‖b‖) + δ := add_le_add hop hint
    _ = δ * K := by dsimp [K]; ring
    _ = ε := div_mul_cancel₀ ε hK.ne'

end KadisonSimilarity

end

end OAI
