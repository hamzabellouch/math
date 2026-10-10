import OAI.NumberTheory.DirichletL.Detector.GramLocalExtension
import OAI.NumberTheory.DirichletL.Detector.GramCommonPhase

namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbeGramCommon
open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge
open CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss
open CenteredMomentCorrelation CenteredMomentCanonical CenteredMomentSupportedCorrelation
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [Fintype ι]

def globalExtension (P : ι→Ideal O) [∀i,(P i).IsMaximal]
    (hg : ∀i,goodLambda∉P i) (c : ι→ℕ) (n₁ n₂ k : O) : ℂ :=
  ∏i,localExtension (P i) (hg i) (c i) n₁ n₂ k

lemma globalExtension_norm (P : ι→Ideal O) [∀i,(P i).IsMaximal]
    (hg : ∀i,goodLambda∉P i) (c : ι→ℕ) (hc : ∀i,1≤c i) (n₁ n₂ k : O) :
    ‖globalExtension P hg c n₁ n₂ k‖≤(Ideal.absNorm (∏i,P i^c i):ℝ) := by
  rw [globalExtension,norm_prod]
  calc
    _ ≤ ∏i,(Ideal.absNorm (P i):ℝ)^c i :=
      Finset.prod_le_prod₀ (fun _ _=>norm_nonneg _) (fun i _=>localExtension_norm (P i) (hg i) (c i) (hc i) n₁ n₂ k)
    _ = _ := by simp only [map_prod,map_pow,Nat.cast_prod,Nat.cast_pow]

theorem globalExtension_periodic (P : ι→Ideal O) [∀i,(P i).IsMaximal]
    (hg : ∀i,goodLambda∉P i) (c : ι→ℕ) (n₁ n₂ m₁ m₂ k l : O)
    (h₁ : n₁-m₁∈∏i,P i) (h₂ : n₂-m₂∈∏i,P i) (hk : k-l∈∏i,P i) :
    globalExtension P hg c n₁ n₂ k=globalExtension P hg c m₁ m₂ l := by
  apply Finset.prod_congr rfl
  intro i hi
  have hle : (∏i,P i)≤P i := Ideal.prod_le_inf.trans (Finset.inf_le (Finset.mem_univ i))
  exact localExtension_periodic (P i) (hg i) (c i) n₁ n₂ m₁ m₂ k l (hle h₁) (hle h₂) (hle hk)

theorem canonical_common_extension (P : ι→Ideal O) [∀i,(P i).IsMaximal]
    (hg : ∀i,goodLambda∉P i) (c : ι→ℕ) (hc : ∀i,1≤c i)
    (hcop : Pairwise (Function.onFun IsCoprime P))
    [Fintype (O⧸∏i,P i^c i)] [∀i,Fintype (O⧸P i^c i)]
    (n₁ n₂ k : O) (hn : IsCoprime n₁ n₂) :
    fullCorrelation (fun x : O⧸∏i,P i^c i=>Ideal.Quotient.mk _ n₂*x)
      (fun y : O⧸∏i,P i^c i=>Ideal.Quotient.mk _ n₁*y)
      (canonicalCRTCharacter P hg c hc hcop) (canonicalCRTCharacter P hg c hc hcop)
      (Ideal.Quotient.mk _ k)=globalExtension P hg c n₁ n₂ k := by
  have hpc : Pairwise (Function.onFun IsCoprime (fun i => P i ^ c i)) := by
    intro i j hij
    exact (hcop hij).pow
  have he := canonicalCRTCorrelation P hg c hc hcop
    (Ideal.Quotient.mk _ n₁) (Ideal.Quotient.mk _ n₂) (Ideal.Quotient.mk _ k)
  have hprod : fullCorrelation (fun x : O⧸∏i,P i^c i=>Ideal.Quotient.mk _ n₂*x)
      (fun y : O⧸∏i,P i^c i=>Ideal.Quotient.mk _ n₁*y)
      (canonicalCRTCharacter P hg c hc hcop) (canonicalCRTCharacter P hg c hc hcop)
      (Ideal.Quotient.mk _ k) =
      ∏i,fullCorrelation (fun x : O⧸P i^c i=>Ideal.Quotient.mk _ n₂*x)
        (fun y : O⧸P i^c i=>Ideal.Quotient.mk _ n₁*y)
        (primePowerRow (P i) (hg i) (hc i)) (primePowerRow (P i) (hg i) (hc i))
        (Ideal.Quotient.mk _ k) := by
    simpa only [IdealGaussCRT.quotientProdEquivPi_mk
      (fun i => P i ^ c i) hpc] using he
  rw [hprod]
  apply Finset.prod_congr rfl
  intro i hi
  apply primePower_common_extension
  by_contra h
  push Not at h
  obtain ⟨a,b,hab⟩ := hn
  have hmem : (1:O)∈P i := by
    rw [←hab]
    exact (P i).add_mem ((P i).mul_mem_left a h.1) ((P i).mul_mem_left b h.2)
  exact (Ideal.IsMaximal.ne_top (I:=P i) inferInstance) ((Ideal.eq_top_iff_one (P i)).mpr hmem)

theorem actualCommon_eq_globalExtension (C : O) (hC : Supported (Ideal.span {C}))
    (P : ι→Ideal O) [∀i,(P i).IsMaximal] (hg : ∀i,goodLambda∉P i)
    (c : ι→ℕ) (hc : ∀i,1≤c i) (hcop : Pairwise (Function.onFun IsCoprime P))
    (he : Ideal.span {C}=∏i,P i^c i)
    [Fintype (O⧸∏i,P i^c i)] [∀i,Fintype (O⧸P i^c i)]
    (n₁ n₂ k : O) (hn : IsCoprime n₁ n₂) :
    actualCommon C hC n₁ n₂ k=globalExtension P hg c n₁ n₂ k := by
  let := finite_quotient_span (supported_element_ne_zero C hC)
  let : Fintype (O⧸Ideal.span {C}) := Fintype.ofFinite _
  let e := Ideal.quotEquivOfEq he
  have hchar : (supportedModulusCharacter C hC : (O⧸Ideal.span {C})→ℂ)=
      (fun x=>canonicalCRTCharacter P hg c hc hcop (e x)) := by
    funext x
    obtain ⟨x,rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [show e (Ideal.Quotient.mk _ x)=Ideal.Quotient.mk _ x from Ideal.quotEquivOfEq_mk he x,
      canonicalCRTCharacter_mk,supportedModulusCharacter_mk,he]
  rw [actualCommon,hchar,fullCorrelation_ringEquiv e]
  simp only [e,Ideal.quotEquivOfEq_mk]
  exact canonical_common_extension P hg c hc hcop n₁ n₂ k hn

end SevenEighths.ProbeGramCommon
end

end OAI
