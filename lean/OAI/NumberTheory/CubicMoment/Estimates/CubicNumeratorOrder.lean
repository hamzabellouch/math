import OAI.NumberTheory.CubicMoment.Estimates.CubicNumeratorCharacter
import OAI.NumberTheory.CubicGram.MixedPoisson
import OAI.NumberTheory.CubicGram.CubeExtraction

namespace OAI

/-! The cubic numerator characters have odd order. In particular a
nonprincipal one is not self-conjugate, as required when excluding the
real-character exceptional term in the prime estimate. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicNumeratorLift_unit_cube {v x : Eisenstein}
    (hx : IsUnit (Ideal.Quotient.mk (modulus (9*v)) x)) :
    cubicNumeratorLift v x ^ 3 = 1 := by
  have hcop := isCoprime_of_residue_isUnit hx
  have h3 : IsCoprime (3:Eisenstein) x := hcop.of_isCoprime_of_dvd_left ⟨3*v,by ring⟩
  have hv : IsCoprime x v := hcop.of_mul_left_right.symm
  have hx3 := residue_isUnit_of_isCoprime h3
  rw [cubicNumeratorLift,ite_eq_left hx3]
  apply cubicSymbol_cube_of_isCoprime (primaryNormalize_primary hx3)
  obtain ⟨u,hu⟩ := primaryNormalize_associated x
  rw [←hu]
  exact (isCoprime_mul_unit_right_left u.isUnit x v).mpr hv

lemma cubicNumeratorChar_cube (hpub : CubicSupplementaryPeriodicity)
    (v : Eisenstein) (hv : v ≠ 0) : cubicNumeratorChar hpub v hv ^ 3 = 1 := by
  apply MulChar.ext
  intro u
  rw [MulChar.pow_apply' _ (by norm_num),MulChar.one_apply u.isUnit]
  change cubicNumeratorLift v (residueRepresentative (9*v) u)^3 = 1
  apply cubicNumeratorLift_unit_cube
  rw [residueRepresentative_spec]
  exact u.isUnit

lemma odd_cubic_character_not_self_conjugate {R : Type*} [CommRing R] [Finite R]
    (χ : MulChar R ℂ) (h3 : χ^3 = 1) (hn : χ ≠ 1) : star χ ≠ χ := by
  intro hs
  have hi : χ⁻¹ = χ := by rw [←MulChar.star_eq_inv,hs]
  have h2 : χ^2 = 1 := by
    calc
      _ = χ*χ⁻¹ := by rw [pow_two,hi]
      _ = 1 := mul_inv_cancel χ
  apply hn
  calc
    χ = χ^2*χ := by rw [h2,one_mul]
    _ = χ^3 := (pow_succ χ 2).symm
    _ = 1 := h3

lemma cubicNumeratorChar_not_self_conjugate (hpub : CubicSupplementaryPeriodicity)
    (v : Eisenstein) (hv : v ≠ 0) (hn : cubicNumeratorChar hpub v hv ≠ 1) :
    star (cubicNumeratorChar hpub v hv) ≠ cubicNumeratorChar hpub v hv := by
  let : Finite (Residues (9*v)) := finite_residues (mul_ne_zero (by norm_num) hv)
  exact odd_cubic_character_not_self_conjugate _ (cubicNumeratorChar_cube hpub v hv) hn

lemma cubicNumeratorChar_ne_one_iff (hpub : CubicSupplementaryPeriodicity)
    (v : Eisenstein) (hv : v ≠ 0) :
    cubicNumeratorChar hpub v hv ≠ 1 ↔ ∃ a : Eisenstein,
      primary a ∧ IsCoprime (9*v) a ∧ cubicSymbol a v ≠ 1 := by
  constructor
  · intro hn
    obtain ⟨u,hu⟩ := MulChar.ne_one_iff.mp hn
    let x := residueRepresentative (9*v) u
    have hx : IsUnit (Ideal.Quotient.mk (modulus (9*v)) x) := by
      simpa only [x,residueRepresentative_spec] using u.isUnit
    have hc := isCoprime_of_residue_isUnit hx
    have hc3 : IsCoprime (3:Eisenstein) x := hc.of_isCoprime_of_dvd_left ⟨3*v,by ring⟩
    have hx3 := residue_isUnit_of_isCoprime hc3
    obtain ⟨w,hw⟩ := primaryNormalize_associated x
    refine ⟨primaryNormalize x,primaryNormalize_primary hx3,?_,?_⟩
    · rw [←hw]
      exact (isCoprime_mul_unit_right_right w.isUnit (9*v) x).mpr hc
    · change cubicNumeratorLift v x ≠ 1 at hu
      simpa only [cubicNumeratorLift,ite_eq_left hx3] using hu
  · rintro ⟨a,ha,hcop,hval⟩ he
    have h := cubicNumeratorChar_primary hpub v hv ha
    rw [he,MulChar.one_apply (residue_isUnit_of_isCoprime hcop)] at h
    exact hval h.symm

lemma cubicNumeratorChar_of_cube (hpub : CubicSupplementaryPeriodicity)
    (v : Eisenstein) (hv : v ≠ 0) (hcube : ∃ j : Eisenstein, j^3 = v) :
    cubicNumeratorChar hpub v hv = 1 := by
  by_contra hn
  obtain ⟨a,ha,hcop,hval⟩ := (cubicNumeratorChar_ne_one_iff hpub v hv).mp hn
  have hac : IsCoprime a v := hcop.of_mul_left_right.symm
  obtain ⟨j,rfl⟩ := hcube
  have haj : IsCoprime a j := hac.of_isCoprime_of_dvd_right ⟨j^2,by ring⟩
  apply hval
  rw [cubicSymbol_pow_upper ha,cubicSymbol_cube_of_isCoprime ha j haj]

lemma nonprincipal_cubicNumerator_not_cube (hpub : CubicSupplementaryPeriodicity)
    (v : Eisenstein) (hv : v ≠ 0) (hn : cubicNumeratorChar hpub v hv ≠ 1) :
    ¬∃ j : Eisenstein, j^3 = v := by
  intro hcube
  exact hn (cubicNumeratorChar_of_cube hpub v hv hcube)

end CubicFirstMoment

end

end OAI
