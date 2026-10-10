import OAI.NumberTheory.DirichletL.Reflection.OriginalWeights
import OAI.NumberTheory.DirichletL.Reflection.InactiveEnergy

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve CanonicalRowCompletion InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

lemma bounded_row_multiplier_energy {κ : Type*} (rows : Finset κ) (r f : κ→ℂ)
    (hr : ∀ k∈rows,‖r k‖≤1) :
    (∑ k∈rows,‖r k*f k‖^2)≤∑ k∈rows,‖f k‖^2 := by
  apply Finset.sum_le_sum
  intro k hk
  apply pow_le_pow_left₀ (norm_nonneg _)
  rw [norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) (hr k hk)

theorem original_frozen_source_energy {κ σ : Type*} [Fintype σ]
    (rows : Finset κ) {m f : Eis} (z : κ→Eis) (D : ∀ k,GoodMaskRowData m f (z k))
    (Ψ : Eis→*ℂ) (Q : Ideal Eis) (hΨ : ∀ n,‖Ψ n‖≤1)
    (c : Eis) (hc : c≠0) [Fintype (Eis⧸Ideal.span {c})]
    (J F Q₀ : Ideal Eis)
    (g : (Eis⧸Ideal.span {c})→Finset (FreeReflection.pool J (Ideal.span {m}*F) Q₀)→Finset σ→κ→ℂ)
    (E : ℝ) (hg : ∀ h A T,(∑ k∈rows,‖g h A T k‖^2)≤E) :
    (∑ k∈rows,‖thetaDerivativeScalar⁻¹*
      ∑ h : Eis⧸Ideal.span {c},fixedThetaRowCoeff c hc ((D k).fixedFactor Ψ Q) h*
        ∑ A : Finset (FreeReflection.pool J (Ideal.span {m}*F) Q₀),
          frozenInactiveWeight J F (Ideal.span {m}*F) Q₀ A*∑ T : Finset σ,g h A T k‖^2)≤
    ‖thetaDerivativeScalar⁻¹‖^2*
      (Fintype.card ((Eis⧸Ideal.span {c})×(Finset (FreeReflection.pool J (Ideal.span {m}*F) Q₀)×Finset σ)):ℝ)^2*E := by
  let B := (Eis⧸Ideal.span {c})×(Finset (FreeReflection.pool J (Ideal.span {m}*F) Q₀)×Finset σ)
  let v := fun (b : B) k => (fixedThetaRowCoeff c hc ((D k).fixedFactor Ψ Q) b.1*
    frozenInactiveWeight J F (Ideal.span {m}*F) Q₀ b.2.1)*g b.1 b.2.1 b.2.2 k
  have hv (b : B) : (∑ k∈rows,‖v b k‖^2)≤E := by
    apply (bounded_row_multiplier_energy rows _ _ (fun k hk =>
      original_fourier_frozen_weight_norm (D k) Ψ Q hΨ c hc b.1 J F Q₀ b.2.1)).trans
    exact hg b.1 b.2.1 b.2.2
  have he := weighted_finite_row_energy_uniform (Finset.univ : Finset B) rows (fun _ => (1:ℂ)) v E (fun b hb => hv b)
  simp only [one_mul,norm_one,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one] at he
  have hid (k : κ) : (∑ b : B,v b k)=
      ∑ h : Eis⧸Ideal.span {c},fixedThetaRowCoeff c hc ((D k).fixedFactor Ψ Q) h*
        ∑ A : Finset (FreeReflection.pool J (Ideal.span {m}*F) Q₀),
          frozenInactiveWeight J F (Ideal.span {m}*F) Q₀ A*∑ T : Finset σ,g h A T k := by
    simp only [B,v,Fintype.sum_prod_type,Finset.mul_sum,mul_assoc]
  simp_rw [←hid]
  simp only [norm_mul,mul_pow,←Finset.mul_sum]
  exact (mul_le_mul_of_nonneg_left he (sq_nonneg _)).trans_eq (by ring)
end
end SevenEighths.InverseReflectedPhase

end OAI
