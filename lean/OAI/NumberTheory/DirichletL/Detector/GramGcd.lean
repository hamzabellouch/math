import OAI.NumberTheory.DirichletL.Detector.GramJointSource

namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbeGramCommon
open CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O
abbrev SupportedIdeal := {I : Id // Supported I}

lemma gram_supported_divisor (I D : Id) (hI : Supported I) (hd : D∣I) : Supported D := by
  obtain ⟨J,rfl⟩ := hd
  exact (supported_mul_iff D J).mp hI |>.1

lemma gram_supported_quotient (I D : Id) (hI : Supported I) (hd : D∣I) :
    Supported (idealQuotient D I) := gram_supported_divisor I _ hI (idealQuotient_dvd hd)

def gcdCommon (I J : SupportedIdeal) : SupportedIdeal :=
  ⟨gcd I.val J.val,gram_supported_divisor I.val _ I.property (gcd_dvd_left _ _)⟩

def gcdLeft (I J : SupportedIdeal) : SupportedIdeal :=
  ⟨idealQuotient (gcdCommon I J).val I.val,
    gram_supported_quotient I.val _ I.property (gcd_dvd_left _ _)⟩

def gcdRight (I J : SupportedIdeal) : SupportedIdeal :=
  ⟨idealQuotient (gcdCommon I J).val J.val,
    gram_supported_quotient J.val _ J.property (gcd_dvd_right _ _)⟩

lemma gcd_residual_coprime (I J : SupportedIdeal) : IsCoprime (gcdLeft I J).val (gcdRight I J).val :=
  (gcd_eq_iff_quotient_coprime _ _ _ (gcdCommon I J).property.1
    (gcd_dvd_left _ _) (gcd_dvd_right _ _)).mp rfl

lemma gcd_common_left (I J : SupportedIdeal) : (gcdCommon I J).val*(gcdLeft I J).val=I.val :=
  idealQuotient_mul (gcd_dvd_left _ _)

lemma gcd_common_right (I J : SupportedIdeal) : (gcdCommon I J).val*(gcdRight I J).val=J.val :=
  idealQuotient_mul (gcd_dvd_right _ _)

abbrev CoprimeTriple := {t : SupportedIdeal×SupportedIdeal×SupportedIdeal // IsCoprime t.2.1.val t.2.2.val}

def gcdTriple (p : SupportedIdeal×SupportedIdeal) : CoprimeTriple :=
  ⟨(gcdCommon p.1 p.2,gcdLeft p.1 p.2,gcdRight p.1 p.2),gcd_residual_coprime p.1 p.2⟩

def multiplyTriple (t : CoprimeTriple) : SupportedIdeal×SupportedIdeal :=
  (⟨t.val.1.val*t.val.2.1.val,(supported_mul_iff _ _).mpr ⟨t.val.1.property,t.val.2.1.property⟩⟩,
   ⟨t.val.1.val*t.val.2.2.val,(supported_mul_iff _ _).mpr ⟨t.val.1.property,t.val.2.2.property⟩⟩)

lemma multiply_gcdTriple (p : SupportedIdeal×SupportedIdeal) : multiplyTriple (gcdTriple p)=p := by
  apply Prod.ext <;> apply Subtype.ext
  · exact gcd_common_left _ _
  · exact gcd_common_right _ _

lemma gcdTriple_multiply (t : CoprimeTriple) : gcdTriple (multiplyTriple t)=t := by
  have he : gcd (t.val.1.val*t.val.2.1.val) (t.val.1.val*t.val.2.2.val)=t.val.1.val := by
    rw [_root_.gcd_mul_left,normalize_eq,Ideal.isCoprime_iff_gcd.mp t.property,mul_one]
  apply Subtype.ext
  apply Prod.ext
  · exact Subtype.ext he
  · apply Prod.ext <;> apply Subtype.ext
    · change idealQuotient (gcd _ _) (t.val.1.val*t.val.2.1.val)=t.val.2.1.val
      dsimp only [multiplyTriple]
      rw [he]
      exact mul_left_cancel₀ t.val.1.property.1 (idealQuotient_mul (dvd_mul_right _ _))
    · change idealQuotient (gcd _ _) (t.val.1.val*t.val.2.2.val)=t.val.2.2.val
      dsimp only [multiplyTriple]
      rw [he]
      exact mul_left_cancel₀ t.val.1.property.1 (idealQuotient_mul (dvd_mul_right _ _))

def gcdPairEquiv : (SupportedIdeal×SupportedIdeal)≃CoprimeTriple where
  toFun := gcdTriple
  invFun := multiplyTriple
  left_inv := multiply_gcdTriple
  right_inv := gcdTriple_multiply

lemma gcdPair_tsum (f : SupportedIdeal×SupportedIdeal→ℂ) :
    (∑'p,f p)=∑'t : CoprimeTriple,f (multiplyTriple t) := by
  exact (gcdPairEquiv.symm.tsum_eq f).symm

end SevenEighths.ProbeGramCommon
end

end OAI
