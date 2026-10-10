import OAI.NumberTheory.DirichletL.Detector.GramCommonSum
import OAI.NumberTheory.DirichletL.Detector.GramCommonLinear
import OAI.NumberTheory.DirichletL.Moments.SupportedCorrelation

namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbeGramCommon
open CenteredMomentCorrelation CenteredMomentSupportedCorrelation
open CenteredMomentCommonSupport CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss ConcreteTraceCRT
local notation "O" => ActualEisensteinCubic.O

def actualCommon (C : O) (hC : Supported (Ideal.span {C})) (n₁ n₂ k : O) : ℂ := by
  letI := finite_quotient_span (supported_element_ne_zero C hC)
  letI : Fintype (ResidueQ C) := Fintype.ofFinite _
  exact fullCorrelation (fun x : ResidueQ C=>Ideal.Quotient.mk _ n₂*x)
    (fun y : ResidueQ C=>Ideal.Quotient.mk _ n₁*y)
    (supportedModulusCharacter C hC) (supportedModulusCharacter C hC) (Ideal.Quotient.mk _ k)

lemma actualCommon_parameter (C : O) (hC : Supported (Ideal.span {C})) (n₁ n₂ a b k : O)
    (hab : a*n₁+b*n₂=1) :
    letI := finite_quotient_span (supported_element_ne_zero C hC)
    letI : Fintype (ResidueQ C) := Fintype.ofFinite _
    actualCommon C hC n₁ n₂ k=
      ∑t : ResidueQ C,
        supportedModulusCharacter C hC (Ideal.Quotient.mk _ (b*k)+Ideal.Quotient.mk _ n₁*t)*
          star (supportedModulusCharacter C hC (Ideal.Quotient.mk _ (-a*k)+Ideal.Quotient.mk _ n₂*t)) := by
  let := finite_quotient_span (supported_element_ne_zero C hC)
  let : Fintype (ResidueQ C) := Fintype.ofFinite _
  have hh : Ideal.Quotient.mk (Ideal.span {C}) a*Ideal.Quotient.mk _ n₁+
      Ideal.Quotient.mk _ b*Ideal.Quotient.mk _ n₂=1 := by rw [←map_mul,←map_mul,←map_add,hab,map_one]
  rw [actualCommon,fullCorrelation_bezout _ _ _ _ _ hh]
  simp only [map_mul,map_neg]

theorem actualCommon_norm (C : O) (hC : Supported (Ideal.span {C})) (n₁ n₂ k : O)
    (hn : IsCoprime n₁ n₂) : ‖actualCommon C hC n₁ n₂ k‖≤(Ideal.absNorm (Ideal.span {C}):ℝ) := by
  obtain ⟨a,b,hab⟩ := hn
  let := finite_quotient_span (supported_element_ne_zero C hC)
  let : Fintype (ResidueQ C) := Fintype.ofFinite _
  have hh : Ideal.Quotient.mk (Ideal.span {C}) a*Ideal.Quotient.mk _ n₁+
      Ideal.Quotient.mk _ b*Ideal.Quotient.mk _ n₂=1 := by rw [←map_mul,←map_mul,←map_add,hab,map_one]
  have hc (x : ResidueQ C) : ‖supportedModulusCharacter C hC x‖≤1 := by
    obtain ⟨x,rfl⟩ := Ideal.Quotient.mk_surjective x
    exact idealRowHom_norm _ _
  have hd := fullCorrelation_bezout_norm (Ideal.Quotient.mk (Ideal.span {C}) n₁)
    (Ideal.Quotient.mk _ n₂) _ _ (Ideal.Quotient.mk _ k) hh
    (supportedModulusCharacter C hC) (supportedModulusCharacter C hC) hc hc
  simpa only [actualCommon,Ideal.absNorm_apply,Submodule.cardQuot_apply,Nat.card_eq_fintype_card] using hd

theorem actual_common_lift_bezout (C n₁ n₂ a b k : O)
    (hC : Supported (Ideal.span {C})) (h₁ : Supported (Ideal.span {n₁}))
    (h₂ : Supported (Ideal.span {n₂})) (hab : a*n₁+b*n₂=1) :
    actualCorrelation (C*n₁) (C*n₂) (supported_mul_elements C n₁ hC h₁)
      (supported_mul_elements C n₂ hC h₂) (C*k)=
      (idealRowHom (b*k) (Ideal.span {n₁})*star (idealRowHom (-a*k) (Ideal.span {n₂})))*
        actualCommon C hC n₁ n₂ k := by
  have hc := supported_element_ne_zero C hC
  have h₁n := supported_element_ne_zero n₁ h₁
  have h₂n := supported_element_ne_zero n₂ h₂
  let := finite_quotient_span hc
  let := finite_quotient_span (mul_ne_zero hc h₁n)
  let := finite_quotient_span (mul_ne_zero hc h₂n)
  let : Fintype (ResidueQ C) := Fintype.ofFinite _
  let : Fintype (ResidueQ (C*n₁)) := Fintype.ofFinite _
  let : Fintype (ResidueQ (C*n₂)) := Fintype.ofFinite _
  change fullModulusCorrelation (C*n₁) (C*n₂) _ _ (C*k)=_
  rw [fullModulusCorrelation_parameter C n₁ n₂ a b k hc h₁n hab,
    actualCommon_parameter C hC n₁ n₂ a b k hab,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t ht
  obtain ⟨t,rfl⟩ := Ideal.Quotient.mk_surjective t
  rw [leftParam_mk,rightParam_mk,supportedModulusCharacter_mul C n₁ hC h₁,
    supportedModulusCharacter_mul C n₂ hC h₂]
  have hleft : idealRowHom (b*k+n₁*t) (Ideal.span {n₁})=idealRowHom (b*k) (Ideal.span {n₁}) := by
    apply idealRowHom_congr_mod
    exact Ideal.mem_span_singleton.mpr ⟨t,by ring⟩
  have hright : idealRowHom (-a*k+n₂*t) (Ideal.span {n₂})=idealRowHom (-a*k) (Ideal.span {n₂}) := by
    apply idealRowHom_congr_mod
    exact Ideal.mem_span_singleton.mpr ⟨t,by ring⟩
  simp only [←map_mul,←map_add]
  simp only [supportedModulusCharacter_mk,hleft,hright,star_mul]
  ring

end SevenEighths.ProbeGramCommon
end

end OAI
