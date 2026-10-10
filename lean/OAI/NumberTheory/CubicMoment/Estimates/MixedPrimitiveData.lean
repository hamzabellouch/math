import OAI.NumberTheory.CubicMoment.Estimates.MixedPrimitiveReduction
import OAI.NumberTheory.CubicMoment.Estimates.PublishedPrimitiveHecke

namespace OAI

/-! Chosen arithmetic data for the actual primitive mixed character.
All fields are proved from the original squarefree coprime pair. -/
noncomputable section
namespace CubicFirstMoment

structure MixedPrimitiveData (a b : Eisenstein) where
  modulus : Eisenstein
  character : MulChar (Residues modulus) ℂ
  modulus_ne_zero : modulus ≠ 0
  primitive : PrimitiveResidueCharacter modulus character
  nonprincipal : character ≠ 1
  norm_bound : normNat modulus ≤ normNat (3*(a*b))
  contains : a*b ∣ modulus
  unit_invariant : ∀ u : Eisensteinˣ, character (Ideal.Quotient.mk (CubicFirstMoment.modulus modulus) u) = 1
  agrees : ∀ x : Eisenstein, primary x → IsCoprime (a*b) x →
    character (Ideal.Quotient.mk (CubicFirstMoment.modulus modulus) x) = mixedCubic a b x

def mixedPrimitiveData {a b : Eisenstein}
    (ha : primary a) (hb : primary b) (hsa : Squarefree a) (hsb : Squarefree b)
    (hab : IsCoprime a b) (hnu : ¬ IsUnit (a*b)) : MixedPrimitiveData a b :=
  Classical.choice (by
    obtain ⟨d,ψ,hd,hprim,hn,hN,hu,_,hagree⟩ := mixed_primitive_conductor ha hb hsa hsb hab hnu
    exact ⟨{ modulus := d
             character := ψ
             modulus_ne_zero := hd
             primitive := hprim
             nonprincipal := hn
             norm_bound := hN
             contains := mixed_conductor_contains ha hb hsa hsb hab ψ hagree
             unit_invariant := hu
             agrees := hagree }⟩)

lemma MixedPrimitiveData.norm_le {a b : Eisenstein} (D : MixedPrimitiveData a b) :
    norm D.modulus ≤ 9*norm a*norm b := by
  have h : norm D.modulus ≤ norm (3*(a*b)) := by
    simpa only [normNat_cast] using (Nat.cast_le (α := ℝ).mpr D.norm_bound)
  have h3 : norm (3:Eisenstein) = 9 := by
    change Complex.normSq (3:ℂ) = 9
    norm_num [Complex.normSq]
  rwa [norm_mul_eq,norm_mul_eq,h3,← mul_assoc] at h

lemma residueHeckeScale_sq {d : Eisenstein} (hd : d ≠ 0) :
    (residueHeckeScale d)^2 = 3*norm d/(2*Real.pi)^2 := by
  unfold residueHeckeScale
  rw [div_pow,Real.sq_sqrt (by positivity [norm_pos_of_ne_zero hd])]

lemma MixedPrimitiveData.scale_sq_le {a b : Eisenstein} (D : MixedPrimitiveData a b) :
    (residueHeckeScale D.modulus)^2 ≤ 27*norm a*norm b/(2*Real.pi)^2 := by
  rw [residueHeckeScale_sq D.modulus_ne_zero]
  apply div_le_div_of_nonneg_right _ (sq_nonneg _)
  nlinarith [D.norm_le]

end CubicFirstMoment

end

end OAI
