import OAI.NumberTheory.DirichletL.Detector.GramJointFixed

namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbeGramCommon
open ProbePhysical CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss RayFourExpansion
open CenteredMomentSupportedCorrelation
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda
variable {ι : Type*} [Fintype ι]

def jointExtension (S : Finset Id) (hS : ∀P∈S,P.IsMaximal) (σ : RayRing)
    (C k : O) (u : Oˣ) (a b : ℕ) (r : O) (hr : Supported (Ideal.span {r}))
    (P : ι→Id) [∀i,(P i).IsMaximal] (hg : ∀i,λ₀∉P i) (c : ι→ℕ) (n₁ n₂ : O) : ℂ :=
  jointFixed S hS σ C u a b r hr n₁ n₂*
    (idealRowHom n₁ (Ideal.span {r})*star (idealRowHom n₂ (Ideal.span {r})))*
      globalExtension P hg c n₁ n₂ k

lemma jointExtension_norm (S : Finset Id) (hS : ∀P∈S,P.IsMaximal) (σ : RayRing)
    (C k : O) (u : Oˣ) (a b : ℕ) (r : O) (hr : Supported (Ideal.span {r}))
    (P : ι→Id) [∀i,(P i).IsMaximal] (hg : ∀i,λ₀∉P i) (c : ι→ℕ) (hc : ∀i,1≤c i)
    (n₁ n₂ : O) : ‖jointExtension S hS σ C k u a b r hr P hg c n₁ n₂‖≤Ideal.absNorm (∏i,P i^c i) := by
  rw [jointExtension,norm_mul]
  have ha : ‖jointFixed S hS σ C u a b r hr n₁ n₂*
      (idealRowHom n₁ (Ideal.span {r})*star (idealRowHom n₂ (Ideal.span {r})))‖≤1 := by
    rw [norm_mul,norm_mul,norm_star]
    exact (mul_le_of_le_one_left (mul_nonneg (norm_nonneg _) (norm_nonneg _))
      (jointFixed_norm _ _ _ _ _ _ _ _ _ _ _)).trans
      ((mul_le_of_le_one_left (norm_nonneg _) (idealRowHom_norm _ _)).trans (idealRowHom_norm _ _))
  exact (mul_le_mul_of_nonneg_right ha (norm_nonneg _)).trans (by simpa using globalExtension_norm P hg c hc n₁ n₂ k)

def jointPeriod (S : Finset Id) (hS : ∀P∈S,P.IsMaximal) (P : ι→Id) (r : O) : Id :=
  jointFixedModulus S hS*(∏i,P i)*Ideal.span {r}

lemma jointExtension_periodic (S : Finset Id) (hS : ∀P∈S,P.IsMaximal) (σ : RayRing)
    (C k : O) (u : Oˣ) (a b : ℕ) (r : O) (hr : Supported (Ideal.span {r}))
    (P : ι→Id) [∀i,(P i).IsMaximal] (hg : ∀i,λ₀∉P i) (c : ι→ℕ)
    (n₁ n₂ m₁ m₂ : O) (h₁ : n₁-m₁∈jointPeriod S hS P r) (h₂ : n₂-m₂∈jointPeriod S hS P r) :
    jointExtension S hS σ C k u a b r hr P hg c n₁ n₂=
      jointExtension S hS σ C k u a b r hr P hg c m₁ m₂ := by
  have hf := jointFixed_periodic S hS σ C u a b r hr n₁ n₂ m₁ m₂
    (Ideal.mul_le_left (Ideal.mul_le_left h₁)) (Ideal.mul_le_left (Ideal.mul_le_left h₂))
  have hm₁ := idealRowHom_congr_mod (Ideal.span {r}) n₁ m₁ (Ideal.mul_le_right h₁)
  have hm₂ := idealRowHom_congr_mod (Ideal.span {r}) n₂ m₂ (Ideal.mul_le_right h₂)
  have he := globalExtension_periodic P hg c n₁ n₂ m₁ m₂ k k
    (Ideal.mul_le_right (Ideal.mul_le_left h₁)) (Ideal.mul_le_right (Ideal.mul_le_left h₂)) (by simp)
  simp only [jointExtension,hf,hm₁,hm₂,he]

lemma jointExtension_dilation_periodic (S : Finset Id) (hS : ∀P∈S,P.IsMaximal) (σ : RayRing)
    (C k : O) (u : Oˣ) (a b : ℕ) (r : O) (hr : Supported (Ideal.span {r}))
    (P : ι→Id) [∀i,(P i).IsMaximal] (hg : ∀i,λ₀∉P i) (c : ι→ℕ)
    (d n₁ n₂ m₁ m₂ : O) (h₁ : n₁-m₁∈jointPeriod S hS P r) (h₂ : n₂-m₂∈jointPeriod S hS P r) :
    jointExtension S hS σ C k u a b r hr P hg c (d*n₁) (d*n₂)=
      jointExtension S hS σ C k u a b r hr P hg c (d*m₁) (d*m₂) := by
  apply jointExtension_periodic
  · rw [←mul_sub];exact (jointPeriod S hS P r).mul_mem_left d h₁
  · rw [←mul_sub];exact (jointPeriod S hS P r).mul_mem_left d h₂

end SevenEighths.ProbeGramCommon
end

end OAI
