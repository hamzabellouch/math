import OAI.NumberTheory.CubicMoment.Estimates.MixedResidueCharacters
import OAI.NumberTheory.CubicGram.CommonFactors
import OAI.NumberTheory.CubicMoment.Estimates.ShortMoebiusPolynomials

namespace OAI

/-! The actual finite character attached to the primary mixed cubic
symbol. Including the modulus 3 makes primary normalization periodic
and removes its dependence on the choice of a unit associate. -/

noncomputable section
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma isCoprime_of_residue_isUnit {q x : Eisenstein}
    (hx : IsUnit (Ideal.Quotient.mk (modulus q) x)) : IsCoprime q x := by
  obtain ⟨u,hu⟩ := hx
  obtain ⟨v,hv⟩ := Ideal.Quotient.mk_surjective (u⁻¹ : (Residues q)ˣ).val
  have he : Ideal.Quotient.mk (modulus q) (x*v) = Ideal.Quotient.mk (modulus q) 1 := by
    rw [map_mul,← hu,hv,map_one]
    exact u.mul_inv
  obtain ⟨w,hw⟩ := Ideal.mem_span_singleton.mp (Ideal.Quotient.eq.mp he)
  refine ⟨-w,v,?_⟩
  linear_combination hw

lemma primaryNormalize_mul_of_residue_units {x y : Eisenstein}
    (hx : IsUnit (Ideal.Quotient.mk (modulus 3) x))
    (hy : IsUnit (Ideal.Quotient.mk (modulus 3) y)) :
    primaryNormalize (x*y) = primaryNormalize x*primaryNormalize y := by
  apply primary_associated_eq
    (primaryNormalize_primary (by rw [map_mul]; exact hx.mul hy))
    (primary_mul (primaryNormalize_primary hx) (primaryNormalize_primary hy))
  exact (primaryNormalize_associated (x*y)).symm.trans
    ((primaryNormalize_associated x).mul_mul (primaryNormalize_associated y))

lemma primaryNormalize_unit {x : Eisenstein} (hx : IsUnit x) : primaryNormalize x = 1 :=
  primary_unit_eq_one ((primaryNormalize_associated x).isUnit_iff.mp hx)
    (primaryNormalize_primary (hx.map (Ideal.Quotient.mk (modulus 3))))

def primaryMixedLift (a b x : Eisenstein) : ℂ :=
  if IsUnit (Ideal.Quotient.mk (modulus 3) x) then
    mixedCubic a b (primaryNormalize x) else 0

lemma primaryMixedLift_primary {a b x : Eisenstein} (hx : primary x) :
    primaryMixedLift a b x = mixedCubic a b x := by
  rw [primaryMixedLift,ite_eq_left (unit_residue_of_dvd_primary hx (dvd_refl x)),
    primaryNormalize_eq_self hx]

lemma primaryMixedLift_one {a b : Eisenstein} (ha : primary a) (hb : primary b) :
    primaryMixedLift a b 1 = 1 := by
  rw [primaryMixedLift_primary (by norm_num [primary]),mixedCubic_one ha hb]

lemma primaryMixedLift_mul {a b : Eisenstein} (ha : primary a) (hb : primary b)
    (x y : Eisenstein) :
    primaryMixedLift a b (x*y) = primaryMixedLift a b x*primaryMixedLift a b y := by
  by_cases hx : IsUnit (Ideal.Quotient.mk (modulus 3) x)
  · by_cases hy : IsUnit (Ideal.Quotient.mk (modulus 3) y)
    · simp only [primaryMixedLift,map_mul,IsUnit.mul_iff,hx,hy,true_and,ite_true]
      rw [primaryNormalize_mul_of_residue_units hx hy,mixedCubic_mul ha hb]
    · simp [primaryMixedLift,map_mul,IsUnit.mul_iff,hx,hy]
  · simp [primaryMixedLift,map_mul,IsUnit.mul_iff,hx]

lemma primaryMixedLift_unit {a b x : Eisenstein} (ha : primary a) (hb : primary b)
    (hx : IsUnit x) : primaryMixedLift a b x = 1 := by
  rw [primaryMixedLift,ite_eq_left (hx.map (Ideal.Quotient.mk (modulus 3))),
    primaryNormalize_unit hx,mixedCubic_one ha hb]

lemma primaryMixedLift_congr_parts {a b x y : Eisenstein}
    (h3 : Ideal.Quotient.mk (modulus 3) x = Ideal.Quotient.mk (modulus 3) y)
    (hq : Ideal.Quotient.mk (modulus (a*b)) x = Ideal.Quotient.mk (modulus (a*b)) y) :
    primaryMixedLift a b x = primaryMixedLift a b y := by
  by_cases hx : IsUnit (Ideal.Quotient.mk (modulus 3) x)
  · have hy : IsUnit (Ideal.Quotient.mk (modulus 3) y) := h3 ▸ hx
    obtain ⟨u,hu⟩ := primaryNormalize_associated x
    have hprim : primary (y*(u:Eisenstein)) := by
      apply (primary_iff_residue_one _).mpr
      rw [map_mul,← h3,← map_mul,hu]
      exact (primary_iff_residue_one _).mp (primaryNormalize_primary hx)
    have hnorm : primaryNormalize y = y*(u:Eisenstein) :=
      primary_associated_eq (primaryNormalize_primary hy) hprim (by
        exact (primaryNormalize_associated y).symm.trans ⟨u,rfl⟩)
    simp only [primaryMixedLift,ite_eq_left hx,ite_eq_left hy]
    rw [hnorm,← hu]
    apply mixedCubic_congr
    rw [map_mul,map_mul,hq]
  · have hy : ¬ IsUnit (Ideal.Quotient.mk (modulus 3) y) := by simpa only [← h3] using hx
    simp only [primaryMixedLift,ite_eq_right hx,ite_eq_right hy]

lemma primaryMixedLift_congr {a b x y : Eisenstein}
    (h : Ideal.Quotient.mk (modulus (3*(a*b))) x =
      Ideal.Quotient.mk (modulus (3*(a*b))) y) :
    primaryMixedLift a b x = primaryMixedLift a b y := by
  have hd : 3*(a*b) ∣ x-y := Ideal.mem_span_singleton.mp (Ideal.Quotient.eq.mp h)
  apply primaryMixedLift_congr_parts
  · exact Ideal.Quotient.eq.mpr (Ideal.mem_span_singleton.mpr ((dvd_mul_right 3 (a*b)).trans hd))
  · exact Ideal.Quotient.eq.mpr (Ideal.mem_span_singleton.mpr ((dvd_mul_left (a*b) 3).trans hd))

lemma primaryMixedLift_nonunit {a b x : Eisenstein} (ha : primary a) (hb : primary b)
    (hx : ¬ IsUnit (Ideal.Quotient.mk (modulus (3*(a*b))) x)) :
    primaryMixedLift a b x = 0 := by
  by_cases h3 : IsUnit (Ideal.Quotient.mk (modulus 3) x)
  · have hq : ¬ IsUnit (Ideal.Quotient.mk (modulus (a*b)) x) := by
      intro hq
      exact hx (residue_isUnit_of_isCoprime
        ((isCoprime_of_residue_isUnit h3).mul_left (isCoprime_of_residue_isUnit hq)))
    rw [primaryMixedLift,ite_eq_left h3]
    apply mixedCubic_eq_zero_of_nonunit ha hb
    intro hn
    obtain ⟨u,hu⟩ := primaryNormalize_associated x
    rw [← hu,map_mul,IsUnit.mul_iff] at hn
    exact hq hn.1
  · simp only [primaryMixedLift,ite_eq_right h3]

/-- The finite residue character agrees with the actual mixed cubic
symbol on primary elements and is trivial on global units. It may still
be imprimitive; conductor reduction is a separate step. -/
def primaryMixedResidueChar (a b : Eisenstein) (ha : primary a) (hb : primary b) :
    MulChar (Residues (3*(a*b))) ℂ where
  toFun v := primaryMixedLift a b (residueRepresentative (3*(a*b)) v)
  map_one' := by
    rw [primaryMixedLift_congr (show
      Ideal.Quotient.mk (modulus (3*(a*b))) (residueRepresentative (3*(a*b)) 1) =
        Ideal.Quotient.mk (modulus (3*(a*b))) 1 by rw [residueRepresentative_spec,map_one])]
    exact primaryMixedLift_one ha hb
  map_mul' v w := by
    rw [primaryMixedLift_congr (show
      Ideal.Quotient.mk (modulus (3*(a*b))) (residueRepresentative (3*(a*b)) (v*w)) =
        Ideal.Quotient.mk (modulus (3*(a*b)))
          (residueRepresentative (3*(a*b)) v*residueRepresentative (3*(a*b)) w) by
            rw [map_mul,residueRepresentative_spec,residueRepresentative_spec,residueRepresentative_spec])]
    exact primaryMixedLift_mul ha hb _ _
  map_nonunit' v hv := primaryMixedLift_nonunit ha hb (by rwa [residueRepresentative_spec])

@[simp] lemma primaryMixedResidueChar_mk {a b : Eisenstein} (ha : primary a) (hb : primary b)
    (x : Eisenstein) :
    primaryMixedResidueChar a b ha hb (Ideal.Quotient.mk (modulus (3*(a*b))) x) =
      primaryMixedLift a b x := primaryMixedLift_congr (residueRepresentative_spec _ _)

lemma primaryMixedResidueChar_primary {a b x : Eisenstein}
    (ha : primary a) (hb : primary b) (hx : primary x) :
    primaryMixedResidueChar a b ha hb (Ideal.Quotient.mk (modulus (3*(a*b))) x) =
      mixedCubic a b x := by rw [primaryMixedResidueChar_mk,primaryMixedLift_primary hx]

lemma primaryMixedResidueChar_trivialInfinity {a b : Eisenstein} (ha : primary a) (hb : primary b) :
    ∀ u : Eisensteinˣ, primaryMixedResidueChar a b ha hb
      (Ideal.Quotient.mk (modulus (3*(a*b))) u) = 1 := by
  intro u
  rw [primaryMixedResidueChar_mk,primaryMixedLift_unit ha hb u.isUnit]


lemma primaryMixedLift_norm_le_one {a b : Eisenstein} (ha : primary a) (hb : primary b)
    (x : Eisenstein) : ‖primaryMixedLift a b x‖ ≤ 1 := by
  unfold primaryMixedLift
  split
  · rw [mixedCubic,norm_mul,norm_star]
    exact (mul_le_mul (norm_cubicSymbol_le_one ha _) (norm_cubicSymbol_le_one hb _)
      (_root_.norm_nonneg _) zero_le_one).trans_eq (one_mul 1)
  · simp

lemma primaryMixedLift_associated {a b x y : Eisenstein}
    (ha : primary a) (hb : primary b) (hxy : Associated x y) :
    primaryMixedLift a b x = primaryMixedLift a b y := by
  obtain ⟨u,hu⟩ := hxy
  rw [← hu,primaryMixedLift_mul ha hb,primaryMixedLift_unit ha hb u.isUnit,mul_one]

lemma star_primaryMixedLift (a b x : Eisenstein) :
    star (primaryMixedLift a b x) = primaryMixedLift b a x := by
  unfold primaryMixedLift
  split <;> simp [mixedCubic,star_mul]

/-- The actual ideal coefficient, with ramified factors explicitly zero. -/
def primaryMixedIdealChar (a b : Eisenstein) (ν : EisensteinIdealExponent) : ℂ :=
  primaryMixedLift a b (idealExponentGenerator ν)

lemma primaryMixedIdealChar_add {a b : Eisenstein} (ha : primary a) (hb : primary b)
    (ν κ : EisensteinIdealExponent) :
    primaryMixedIdealChar a b (ν+κ) = primaryMixedIdealChar a b ν*primaryMixedIdealChar a b κ := by
  rw [primaryMixedIdealChar,idealExponentGenerator_add,primaryMixedLift_mul ha hb]
  rfl

lemma primaryMixedIdealChar_at_element {a b x : Eisenstein}
    (ha : primary a) (hb : primary b) (hx : primary x) :
    primaryMixedIdealChar a b (idealExponentOf x) = mixedCubic a b x := by
  rw [primaryMixedIdealChar,
    primaryMixedLift_associated ha hb (idealExponentOf_associated (primary_ne_zero hx)),
    primaryMixedLift_primary hx]

lemma primaryMixedIdealChar_norm_le_one {a b : Eisenstein}
    (ha : primary a) (hb : primary b) (ν : EisensteinIdealExponent) :
    ‖primaryMixedIdealChar a b ν‖ ≤ 1 := primaryMixedLift_norm_le_one ha hb _

lemma star_primaryMixedIdealChar (a b : Eisenstein) (ν : EisensteinIdealExponent) :
    star (primaryMixedIdealChar a b ν) = primaryMixedIdealChar b a ν :=
  star_primaryMixedLift _ _ _

end CubicFirstMoment

end

end OAI
