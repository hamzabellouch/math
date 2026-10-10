import OAI.NumberTheory.DirichletL.Detector.GramCommonActual

namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbeGramCommon
open CenteredMomentCorrelation CenteredMomentSupportedCorrelation CenteredMomentCommonSupport
open CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss ConcreteTraceCRT
local notation "O" => ActualEisensteinCubic.O

lemma supported_bezout_inverse (n m a b : O) (hn : Supported (Ideal.span {n}))
    (hab : a*n+b*m=1) :
    idealRowHom b (Ideal.span {n})=star (idealRowHom m (Ideal.span {n})) := by
  have he : idealRowHom (b*m) (Ideal.span {n})=1 := by
    rw [←idealRowHom_one_supported (Ideal.span {n}) hn]
    apply idealRowHom_congr_mod
    apply Ideal.mem_span_singleton.mpr
    refine ⟨-a,?_⟩
    linear_combination hab
  rw [idealRowHom_argument_mul] at he
  let := finite_quotient_span (supported_element_ne_zero n hn)
  let : Fintype (ResidueQ n) := Fintype.ofFinite _
  change supportedModulusCharacter n hn (Ideal.Quotient.mk _ b)=
    star (supportedModulusCharacter n hn (Ideal.Quotient.mk _ m))
  rw [MulChar.star_apply',MulChar.inv_apply_eq_inv']
  exact eq_inv_of_mul_eq_one_left he

theorem actual_common_lift (C n₁ n₂ k : O)
    (hC : Supported (Ideal.span {C})) (h₁ : Supported (Ideal.span {n₁}))
    (h₂ : Supported (Ideal.span {n₂}))
    (hp₁ : ConcretePrimeRowBridge.goodLambda^2∣n₁-1)
    (hp₂ : ConcretePrimeRowBridge.goodLambda^2∣n₂-1) (hn : IsCoprime n₁ n₂) :
    actualCorrelation (C*n₁) (C*n₂) (supported_mul_elements C n₁ hC h₁)
      (supported_mul_elements C n₂ hC h₂) (C*k)=
      idealRowHom k (Ideal.span {n₁})*star (idealRowHom (-k) (Ideal.span {n₂}))*
        sexticReciprocityPhase n₁ n₂*actualCommon C hC n₁ n₂ k := by
  obtain ⟨a,b,hab⟩ := hn
  rw [actual_common_lift_bezout C n₁ n₂ a b k hC h₁ h₂ hab]
  have h₁b := supported_bezout_inverse n₁ n₂ a b h₁ hab
  have h₂a := supported_bezout_inverse n₂ n₁ b a h₂ (by simpa only [add_comm] using hab)
  have he : idealRowHom (-a*k) (Ideal.span {n₂})=
      idealRowHom a (Ideal.span {n₂})*idealRowHom (-k) (Ideal.span {n₂}) := by
    rw [show -a*k=a*(-k) by ring,idealRowHom_argument_mul]
  rw [idealRowHom_argument_mul,he,h₁b,h₂a,star_mul,star_star]
  let := finite_quotient_span (supported_element_ne_zero n₁ h₁)
  let : Fintype (ResidueQ n₁) := Fintype.ofFinite _
  have hphase := supported_opposite_phase n₁ n₂ h₁ h₂ hp₁ hp₂ ⟨a,b,hab⟩
  calc
    _ = idealRowHom k (Ideal.span {n₁})*star (idealRowHom (-k) (Ideal.span {n₂}))*
        (idealRowHom n₁ (Ideal.span {n₂})*star (idealRowHom n₂ (Ideal.span {n₁})))*actualCommon C hC n₁ n₂ k := by ring
    _ = _ := by rw [hphase]

theorem actual_common_norm (C n₁ n₂ k : O)
    (hC : Supported (Ideal.span {C})) (h₁ : Supported (Ideal.span {n₁}))
    (h₂ : Supported (Ideal.span {n₂})) (hn : IsCoprime n₁ n₂) :
    ‖actualCorrelation (C*n₁) (C*n₂) (supported_mul_elements C n₁ hC h₁)
      (supported_mul_elements C n₂ hC h₂) (C*k)‖≤(Ideal.absNorm (Ideal.span {C}):ℝ) := by
  obtain ⟨a,b,hab⟩ := hn
  rw [actual_common_lift_bezout C n₁ n₂ a b k hC h₁ h₂ hab,norm_mul,norm_mul,norm_star]
  have hc := actualCommon_norm C hC n₁ n₂ k ⟨a,b,hab⟩
  have hp : ‖idealRowHom (b*k) (Ideal.span {n₁})‖*‖idealRowHom (-a*k) (Ideal.span {n₂})‖≤1 :=
    (mul_le_of_le_one_left (norm_nonneg _) (idealRowHom_norm _ _)).trans (idealRowHom_norm _ _)
  exact (mul_le_mul_of_nonneg_right hp (norm_nonneg _)).trans (by simpa using hc)

end SevenEighths.ProbeGramCommon
end

end OAI
