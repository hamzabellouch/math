import OAI.NumberTheory.DirichletL.Detector.GramNumerator

namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbeGramCommon
open ProbePhysical CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss RayFourExpansion
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda

def primaryCoefficient (S : Finset Id) (hS : ∀P∈S,P.IsMaximal) (σ : RayRing) (n : O) : ℂ :=
  if λ₀^2∣n-1 then gramCoefficientExtension S hS σ n else 0

lemma primaryCoefficient_norm (S : Finset Id) (hS : ∀P∈S,P.IsMaximal) (σ : RayRing) (n : O) :
    ‖primaryCoefficient S hS σ n‖≤1 := by
  unfold primaryCoefficient
  split_ifs
  · exact gramCoefficientExtension_norm _ _ _ _
  · simp

def jointFixedModulus (S : Finset Id) (hS : ∀P∈S,P.IsMaximal) : Id :=
  gramFixedModulus S hS*Ideal.span {λ₀^2}*Ideal.span {(72:O)}

lemma jointFixedModulus_nonzero (S : Finset Id) (hS : ∀P∈S,P.IsMaximal) : jointFixedModulus S hS≠0 := by
  apply mul_ne_zero
  · apply mul_ne_zero (gramFixedModulus_nonzero S hS)
    exact Ideal.span_singleton_eq_bot.not.mpr (pow_ne_zero _ ConcretePrimeRowBridge.goodLambda_prime.ne_zero)
  · exact Ideal.span_singleton_eq_bot.not.mpr (by norm_num)

lemma primaryCoefficient_periodic (S : Finset Id) (hS : ∀P∈S,P.IsMaximal)
    (σ : RayRing) (x y : O) (hxy : x-y∈jointFixedModulus S hS) :
    primaryCoefficient S hS σ x=primaryCoefficient S hS σ y := by
  have hg := gramCoefficientExtension_periodic S hS σ x y (Ideal.mul_le_left (Ideal.mul_le_left hxy))
  have hp : λ₀^2∣x-y := Ideal.mem_span_singleton.mp (Ideal.mul_le_right (Ideal.mul_le_left hxy))
  have hi : (λ₀^2∣x-1)↔(λ₀^2∣y-1) := by
    constructor
    · intro h
      convert dvd_sub h hp using 1 ; ring
    · intro h
      convert dvd_add hp h using 1 ; ring
  simp only [primaryCoefficient,hi,hg]

def jointFixed (S : Finset Id) (hS : ∀P∈S,P.IsMaximal) (σ : RayRing)
    (C : O) (u : Oˣ) (a b : ℕ) (r : O) (hr : Supported (Ideal.span {r})) (n₁ n₂ : O) : ℂ :=
  primaryCoefficient S hS σ (C*n₁)*star (primaryCoefficient S hS σ (C*n₂))*
    numeratorBadTwist u a b r hr n₁*star (numeratorBadTwist (-u) a b r hr n₂)*
      sexticReciprocityPhase n₁ n₂

lemma jointFixed_norm (S : Finset Id) (hS : ∀P∈S,P.IsMaximal) (σ : RayRing)
    (C : O) (u : Oˣ) (a b : ℕ) (r : O) (hr : Supported (Ideal.span {r})) (n₁ n₂ : O) :
    ‖jointFixed S hS σ C u a b r hr n₁ n₂‖≤1 := by
  unfold jointFixed
  simp only [norm_mul,norm_star]
  refine (mul_le_of_le_one_left (norm_nonneg _) ?_).trans (sexticReciprocityPhase_norm _ _)
  refine (mul_le_of_le_one_left (norm_nonneg _) ?_).trans (numeratorBadTwist_norm _ _ _ _ _ _)
  refine (mul_le_of_le_one_left (norm_nonneg _) ?_).trans (numeratorBadTwist_norm _ _ _ _ _ _)
  exact (mul_le_of_le_one_left (norm_nonneg _) (primaryCoefficient_norm _ _ _ _)).trans (primaryCoefficient_norm _ _ _ _)

lemma jointFixed_periodic (S : Finset Id) (hS : ∀P∈S,P.IsMaximal) (σ : RayRing)
    (C : O) (u : Oˣ) (a b : ℕ) (r : O) (hr : Supported (Ideal.span {r})) (n₁ n₂ m₁ m₂ : O)
    (h₁ : n₁-m₁∈jointFixedModulus S hS) (h₂ : n₂-m₂∈jointFixedModulus S hS) :
    jointFixed S hS σ C u a b r hr n₁ n₂=jointFixed S hS σ C u a b r hr m₁ m₂ := by
  have hc₁ := primaryCoefficient_periodic S hS σ (C*n₁) (C*m₁)
    (by rw [←mul_sub];exact (jointFixedModulus S hS).mul_mem_left C h₁)
  have hc₂ := primaryCoefficient_periodic S hS σ (C*n₂) (C*m₂)
    (by rw [←mul_sub];exact (jointFixedModulus S hS).mul_mem_left C h₂)
  have hb₁ := numeratorBadTwist_periodic u a b r hr n₁ m₁ (Ideal.mul_le_right h₁)
  have hb₂ := numeratorBadTwist_periodic (-u) a b r hr n₂ m₂ (Ideal.mul_le_right h₂)
  have hfour (x y : O) (h : x-y∈jointFixedModulus S hS) : (4:O)∣x-y :=
    (show (4:O)∣72 from ⟨18,by norm_num⟩).trans (Ideal.mem_span_singleton.mp (Ideal.mul_le_right h))
  have hp : sexticReciprocityPhase n₁ n₂=sexticReciprocityPhase m₁ m₂ := by
    unfold sexticReciprocityPhase
    rw [QuadraticGaussRay.residue_eq_of_four_dvd_sub n₁ m₁ (hfour _ _ h₁),
      QuadraticGaussRay.residue_eq_of_four_dvd_sub n₂ m₂ (hfour _ _ h₂)]
  simp only [jointFixed,hc₁,hc₂,hb₁,hb₂,hp]

end SevenEighths.ProbeGramCommon
end

end OAI
