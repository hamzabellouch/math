import OAI.NumberTheory.CubicMoment.Estimates.PublishedHecke
import OAI.NumberTheory.CubicGram.MixedPoisson
import OAI.NumberTheory.CubicMoment.Estimates.PublishedAdditiveSieve

namespace OAI

/-! The actual mixed cubic residue characters and their finite Fourier transform. -/

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma mixedCubic_congr {a b v w : Eisenstein}
    (h : Ideal.Quotient.mk (modulus (a*b)) v = Ideal.Quotient.mk (modulus (a*b)) w) :
    mixedCubic a b v = mixedCubic a b w := mixedSymbol_congr h

lemma mixedCubic_eq_zero_of_nonunit {a b : Eisenstein} (ha : primary a) (hb : primary b)
    (v : Eisenstein) (hv : ¬ IsUnit (Ideal.Quotient.mk (modulus (a*b)) v)) :
    mixedCubic a b v = 0 := by
  by_cases hav : IsCoprime a v
  · have hbv : ¬ IsCoprime b v := fun h => hv (residue_isUnit_of_isCoprime (hav.mul_left h))
    simp [mixedCubic,cubicSymbol_eq_zero_of_not_isCoprime hb hbv]
  · simp [mixedCubic,cubicSymbol_eq_zero_of_not_isCoprime ha hav]

/-- This character is defined at composite conductors, rather than supplied as
an abstract character agreeing with the desired cubic symbol. -/
def mixedResidueChar (a b : Eisenstein) (ha : primary a) (hb : primary b) :
    MulChar (Residues (a*b)) ℂ where
  toFun x := mixedCubic a b (residueRepresentative (a*b) x)
  map_one' := by
    rw [mixedCubic_congr (show
      Ideal.Quotient.mk (modulus (a*b)) (residueRepresentative (a*b) 1) =
      Ideal.Quotient.mk (modulus (a*b)) 1 by rw [residueRepresentative_spec,map_one])]
    exact mixedCubic_one ha hb
  map_mul' x y := by
    rw [mixedCubic_congr (show
      Ideal.Quotient.mk (modulus (a*b)) (residueRepresentative (a*b) (x*y)) =
      Ideal.Quotient.mk (modulus (a*b))
        (residueRepresentative (a*b) x*residueRepresentative (a*b) y) by
          rw [map_mul,residueRepresentative_spec,residueRepresentative_spec,
            residueRepresentative_spec])]
    exact mixedCubic_mul ha hb _ _
  map_nonunit' x hx := mixedCubic_eq_zero_of_nonunit ha hb _ (by
    rwa [residueRepresentative_spec])

@[simp] lemma mixedResidueChar_mk {a b : Eisenstein} (ha : primary a) (hb : primary b)
    (v : Eisenstein) :
    mixedResidueChar a b ha hb (Ideal.Quotient.mk (modulus (a*b)) v) =
      mixedCubic a b v := mixedCubic_congr (residueRepresentative_spec _ _)

lemma huxleyPhase_eq_fourierChar (q h n : Eisenstein) :
    huxleyPhase q h n = (Real.fourierChar
      (tracePair (n:ℂ) ((h:ℂ)/((q:ℂ)*traceLambda))) : ℂ) := by
  rw [Real.fourierChar_apply]
  unfold huxleyPhase tracePair
  dsimp only
  have hz (z : ℂ) : z+star z = (2*z.re:ℝ) := by
    apply Complex.ext <;> simp
    ring
  rw [hz]
  congr 1
  push_cast
  rw [show (n:ℂ)*(h:ℂ)/(traceLambda*(q:ℂ)) =
    (n:ℂ)*((h:ℂ)/((q:ℂ)*traceLambda)) by ring]
  ring

/-- The raw Gauss transform has exactly the conductor square-root factor.
This identity holds also at nonunit frequencies (where the right side vanishes). -/
theorem mixedResidueChar_fourier {a b : Eisenstein} (ha : primary a) (hb : primary b)
    (hsa : Squarefree a) (hsb : Squarefree b) (hab : IsCoprime a b)
    [Fintype (Residues (a*b))] (n : Eisenstein) :
    (∑ x : Residues (a*b), mixedResidueChar a b ha hb x *
      huxleyPhase (a*b) (residueRepresentative (a*b) x) n) =
      ((Real.sqrt (norm (a*b)):ℂ)*(gauss a*star (gauss b)) /
        mixedCubic a b 3) * star (mixedCubic a b n) := by
  have hc : IsCoprime (a*b) 3 := by
    obtain ⟨k,hk⟩ := primary_mul ha hb
    refine ⟨1,-k,?_⟩
    linear_combination hk
  have hc3 : ‖mixedCubic a b 3‖ = 1 := mixedCubic_norm_of_coprime ha hb hc
  have hc30 : mixedCubic a b 3 ≠ 0 := norm_ne_zero_iff.mp (by rw [hc3]; norm_num)
  have hphase (x : Residues (a*b)) :
      huxleyPhase (a*b) (residueRepresentative (a*b) x) n =
      (Real.fourierChar (tracePair (residueRepresentative (a*b) x:ℂ)
        ((n:ℂ)/(((a*b:Eisenstein):ℂ)*traceLambda))) : ℂ) := by
    rw [huxleyPhase_eq_fourierChar]
    congr 2
    unfold tracePair
    congr 2
    ring
  have hsum : mixedCubic a b 3 * (∑ x : Residues (a*b), mixedResidueChar a b ha hb x *
      huxleyPhase (a*b) (residueRepresentative (a*b) x) n) =
      primaryMixedFourier a b n := by
    rw [primaryMixedFourier,tsum_fintype,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x hx
    rw [hphase]
    change mixedCubic a b 3 * (mixedCubic a b (residueRepresentative (a*b) x) * _) =
      mixedCubic a b (3*residueRepresentative (a*b) x) * _
    rw [mixedCubic_mul ha hb]
    ring
  apply (mul_left_cancel₀ hc30)
  rw [hsum,primaryMixedFourier_squarefree ha hb hsa hsb hab]
  field_simp [hc30]
  simp only [mixedCubic,star_mul,star_star]
  ring

end CubicFirstMoment

end

end OAI
