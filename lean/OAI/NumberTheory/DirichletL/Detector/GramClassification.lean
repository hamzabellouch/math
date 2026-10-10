import OAI.NumberTheory.DirichletL.Detector.GramCanonical
import OAI.NumberTheory.DirichletL.CenteredExceptionalProfile

namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbeGramCommon
open CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss UniqueFactorizationMonoid
open CenteredExceptionalCount
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda

def exceptionalModulus (S : Finset Id) (hS : ∀p∈S,p.IsMaximal) (C : SupportedIdeal) : Id :=
  jointFixedModulus S hS*C.val
lemma exceptionalModulus_nonzero (S : Finset Id) (hS : ∀p∈S,p.IsMaximal) (C : SupportedIdeal) :
    exceptionalModulus S hS C≠0 := mul_ne_zero (jointFixedModulus_nonzero S hS) C.property.1
lemma exceptionalModulus_norm (S : Finset Id) (hS : ∀p∈S,p.IsMaximal) (C : SupportedIdeal) :
    Ideal.absNorm (exceptionalModulus S hS C)=Ideal.absNorm (jointFixedModulus S hS)*Ideal.absNorm C.val :=
  map_mul Ideal.absNorm _ _

def ExceptionalFrequency (S : Finset Id) (hS : ∀p∈S,p.IsMaximal) (C : SupportedIdeal) (k : GramFrequency) : Prop :=
  ∀p∉IdealMobiusDivisorSum.primeSupport (exceptionalModulus S hS C),valuation (Ideal.span {k.val}) p%6=0

lemma nonexceptional_prime (S : Finset Id) (hS : ∀p∈S,p.IsMaximal) (C : SupportedIdeal) (k : GramFrequency)
    (hk : ¬ExceptionalFrequency S hS C k) :
    ∃p : Id,Prime p ∧ p∉IdealMobiusDivisorSum.primeSupport (exceptionalModulus S hS C) ∧
      ¬6∣(normalizedFactors (Ideal.span {k.val})).count p := by
  unfold ExceptionalFrequency at hk
  push Not at hk
  obtain ⟨p,hp,he⟩ := hk
  have hcount : (normalizedFactors (Ideal.span {k.val})).count p≠0 := by
    intro hz
    apply he
    simp [valuation,hz]
  have hprime := prime_of_normalized_factor p (Multiset.count_pos.mp (Nat.pos_of_ne_zero hcount))
  exact ⟨p,hprime,hp,fun hd=>he (Nat.mod_eq_zero_of_dvd hd)⟩

lemma outside_exceptional_not_dvd (S : Finset Id) (hS : ∀p∈S,p.IsMaximal) (C : SupportedIdeal)
    (p : Id) (hp : Prime p) (hout : p∉IdealMobiusDivisorSum.primeSupport (exceptionalModulus S hS C)) :
    (¬p∣jointFixedModulus S hS) ∧ (¬p∣∏i : GramPrime C,gramPrime C i) := by
  have hnot : ¬p∣exceptionalModulus S hS C := by
    intro hd
    apply hout
    exact Multiset.mem_toFinset.mpr ((Ideal.mem_normalizedFactors_iff (exceptionalModulus_nonzero S hS C)).mpr
      ⟨Ideal.isPrime_of_prime hp,Ideal.dvd_iff_le.mp hd⟩)
  refine ⟨fun hd=>hnot (dvd_mul_of_dvd_left hd _),?_⟩
  intro hd
  apply hnot
  apply dvd_mul_of_dvd_right
  apply dvd_trans hd
  calc
    _∣∏i : GramPrime C,gramPrime C i^gramExponent C i :=
      Finset.prod_dvd_prod_of_dvd _ _ (fun i _=>dvd_pow_self _ (Nat.one_le_iff_ne_zero.mp (gramExponent_pos C i)))
    _=C.val := (gramPrime_product C).symm

lemma outside_exceptional_good (S : Finset Id) (hS : ∀p∈S,p.IsMaximal) (C : SupportedIdeal)
    (p : Id) (hp : Prime p) (hout : p∉IdealMobiusDivisorSum.primeSupport (exceptionalModulus S hS C)) :
    λ₀∉p ∧ ringChar (O⧸p)≠2 := by
  let : p.IsMaximal := (Ideal.isPrime_of_prime hp).isMaximal hp.ne_zero
  have hle : exceptionalModulus S hS C≤Ideal.span {(72:O)} :=
    le_trans Ideal.mul_le_left Ideal.mul_le_right
  have hh := CenteredExceptionalProfile.outside_fixed_support _ (exceptionalModulus_nonzero S hS C) hle p hp hout
  exact ⟨hh.1,ActualEisensteinCubic.quotient_char_ne_two_of_two_not_mem p hh.2.1⟩

end SevenEighths.ProbeGramCommon
end

end OAI
