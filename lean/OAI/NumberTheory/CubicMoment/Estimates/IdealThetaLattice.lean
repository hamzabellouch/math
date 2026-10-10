import OAI.NumberTheory.CubicMoment.Estimates.IdealThetaDecay
import OAI.NumberTheory.CubicMoment.Estimates.ResidueIdealCharacters
import OAI.NumberTheory.CubicMoment.Estimates.ShortMoebiusFinite

namespace OAI

/-! Exact ideal-to-element reindexing for a unit-invariant residue theta series. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

lemma idealTheta_units_finite : Finite (Eisensteinˣ) := by
  let f : Eisensteinˣ → {u : Eisenstein // u ∈ nonzeroNormBall 1} := fun u =>
    ⟨u,mem_nonzeroNormBall.mpr ⟨by rw [norm_of_isUnit u.isUnit],u.ne_zero⟩⟩
  exact Finite.of_injective f (fun u v h => Units.ext (congrArg Subtype.val h))

lemma idealExponentOf_unit_mul (ν : EisensteinIdealExponent) (u : Eisensteinˣ) :
    idealExponentOf ((u:Eisenstein)*idealExponentGenerator ν) = ν := by
  have ha : Associated (idealExponentGenerator ν) ((u:Eisenstein)*idealExponentGenerator ν) :=
    ⟨u,mul_comm _ _⟩
  exact (idealExponentOf_eq_of_associated
    (mul_ne_zero u.ne_zero (idealExponentGenerator_ne_zero ν))
    (idealExponentGenerator_ne_zero ν) ha.symm).trans (idealExponentOf_generator ν)

lemma idealElementCoordinates_bijective : Function.Bijective
    (fun x : EisensteinIdealExponent × Eisensteinˣ =>
      (⟨(x.2:Eisenstein)*idealExponentGenerator x.1,
        mul_ne_zero x.2.ne_zero (idealExponentGenerator_ne_zero x.1)⟩ :
        {a : Eisenstein // a ≠ 0})) := by
  constructor
  · intro x y h
    have he := congrArg Subtype.val h
    have hv : x.1 = y.1 := by
      simpa only [idealExponentOf_unit_mul] using congrArg idealExponentOf he
    rcases x with ⟨ν,u⟩
    rcases y with ⟨κ,v⟩
    dsimp only at hv he
    subst κ
    exact congrArg (fun w : Eisensteinˣ => (ν,w))
      (Units.ext (mul_right_cancel₀ (idealExponentGenerator_ne_zero ν) he))
  · intro a
    obtain ⟨u,hu⟩ := idealExponentOf_associated a.property
    refine ⟨(idealExponentOf a.val,u),Subtype.ext ?_⟩
    simpa only [mul_comm] using hu

def idealElementCoordinates : (EisensteinIdealExponent × Eisensteinˣ) ≃
    {a : Eisenstein // a ≠ 0} := Equiv.ofBijective _ idealElementCoordinates_bijective

lemma idealElementCoordinates_norm (x : EisensteinIdealExponent × Eisensteinˣ) :
    norm (idealElementCoordinates x).val = idealExponentNorm x.1 := by
  change norm ((x.2:Eisenstein)*idealExponentGenerator x.1) = _
  rw [← normNat_cast,normNat_mul,normNat_of_isUnit x.2.isUnit]
  simp only [Nat.one_mul]
  rfl

lemma residue_char_unit_mul (q : Eisenstein) (χ : MulChar (Residues q) ℂ)
    (hu : ∀ u : Eisensteinˣ, χ (Ideal.Quotient.mk (modulus q) u) = 1)
    (x : EisensteinIdealExponent × Eisensteinˣ) :
    χ (Ideal.Quotient.mk (modulus q) (idealElementCoordinates x).val) = residueIdealChar q χ x.1 := by
  change χ (Ideal.Quotient.mk (modulus q) ((x.2:Eisenstein)*idealExponentGenerator x.1)) = _
  rw [map_mul,map_mul,hu,one_mul]
  rfl

lemma idealTheta_lattice {q : Eisenstein} (hq : q ≠ 0)
    (χ : MulChar (Residues q) ℂ)
    (hu : ∀ u : Eisensteinˣ, χ (Ideal.Quotient.mk (modulus q) u) = 1)
    {A t : ℝ} (hA : 0 < A) (ht : 0 < t) :
    (∑' a : {a : Eisenstein // a ≠ 0},
      χ (Ideal.Quotient.mk (modulus q) a.val)*(Real.exp (-norm a.val*t/A):ℝ)) =
      (Nat.card (Eisensteinˣ):ℂ)*idealTheta A (residueIdealChar q χ) t := by
  let : Finite (Eisensteinˣ) := idealTheta_units_finite
  let : Fintype (Eisensteinˣ) := Fintype.ofFinite _
  let f : EisensteinIdealExponent → ℂ := fun ν =>
    residueIdealChar q χ ν*(Real.exp (-idealExponentNorm ν*t/A):ℝ)
  have hf : Summable f := idealTheta_summable hA ht _ (residueIdealChar_norm_le_one hq χ)
  have hprod : Summable (fun x : EisensteinIdealExponent × Eisensteinˣ => f x.1) := by
    simpa only [mul_one] using summable_mul_of_summable_norm
      (g := fun _ : Eisensteinˣ => (1:ℂ)) hf.norm (hasSum_fintype _).summable
  rw [← idealElementCoordinates.tsum_eq]
  have he : (fun x : EisensteinIdealExponent × Eisensteinˣ =>
      χ (Ideal.Quotient.mk (modulus q) (idealElementCoordinates x).val)*
        (Real.exp (-norm (idealElementCoordinates x).val*t/A):ℝ)) = fun x => f x.1 := by
    funext x
    rw [residue_char_unit_mul q χ hu,idealElementCoordinates_norm]
  rw [he,hprod.tsum_prod' (fun _ => (hasSum_fintype _).summable)]
  simp only [tsum_fintype,Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  rw [tsum_mul_left]
  simp only [Nat.card_eq_fintype_card]
  rfl

end CubicFirstMoment

end

end OAI
