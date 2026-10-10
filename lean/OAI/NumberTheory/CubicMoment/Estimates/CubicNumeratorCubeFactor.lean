import OAI.NumberTheory.CubicMoment.Estimates.CubicNumeratorConductor

namespace OAI

/-! Multiplication by a nonzero cube changes only deleted Euler factors,
not principality of the cubic numerator character. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicNumeratorChar_mul_cube_ne_one (hpub : CubicSupplementaryPeriodicity)
    {r c : Eisenstein} (hr : r ≠ 0) (hc : c ≠ 0)
    (hn : cubicNumeratorChar hpub r hr ≠ 1) :
    cubicNumeratorChar hpub (r*c^3) (mul_ne_zero hr (pow_ne_zero _ hc)) ≠ 1 := by
  obtain ⟨x,hx,hcop,hne⟩ := (cubicNumeratorChar_ne_one_iff hpub r hr).mp hn
  obtain ⟨y,hy,hcy⟩ := exists_coprime_residue_lift hc hcop
  have hyx : (3:Eisenstein) ∣ y-x :=
    (show (3:Eisenstein) ∣ 9*r from ⟨3*r,by ring⟩).trans hy
  have hyp : primary y := by
    change (3:Eisenstein) ∣ y-1
    convert dvd_add hyx hx using 1
    ring
  have hyc : IsCoprime y c := hcy.of_mul_left_right.symm
  have hyr : IsCoprime r y := hcy.of_mul_left_left.of_mul_left_right
  have hy9 : IsCoprime (9:Eisenstein) y := hcy.of_mul_left_left.of_mul_left_left
  apply (cubicNumeratorChar_ne_one_iff hpub (r*c^3) (mul_ne_zero hr (pow_ne_zero _ hc))).mpr
  refine ⟨y,hyp,hy9.mul_left (hyr.mul_left (hyc.symm.pow_left (m := 3))),?_⟩
  rw [cubicSymbol_mul_upper hyp,cubicSymbol_pow_upper hyp,
    cubicSymbol_cube_of_isCoprime hyp c hyc,mul_one,hpub r hr y x hyp hx hy]
  exact hne

lemma cubicNumeratorChar_mul_cube_ne_one_iff (hpub : CubicSupplementaryPeriodicity)
    {r c : Eisenstein} (hr : r ≠ 0) (hc : c ≠ 0) :
    cubicNumeratorChar hpub (r*c^3) (mul_ne_zero hr (pow_ne_zero _ hc)) ≠ 1 ↔
      cubicNumeratorChar hpub r hr ≠ 1 := by
  constructor
  · intro hn
    obtain ⟨x,hx,hcop,hne⟩ :=
      (cubicNumeratorChar_ne_one_iff hpub (r*c^3) (mul_ne_zero hr (pow_ne_zero _ hc))).mp hn
    have hxr : IsCoprime r x := hcop.of_mul_left_right.of_mul_left_left
    have hxc : IsCoprime x c :=
      (hcop.of_mul_left_right.of_mul_left_right).of_isCoprime_of_dvd_left (dvd_pow_self c (by norm_num : 3 ≠ 0)) |>.symm
    have hx9 : IsCoprime (9:Eisenstein) x := hcop.of_mul_left_left
    apply (cubicNumeratorChar_ne_one_iff hpub r hr).mpr
    refine ⟨x,hx,hx9.mul_left hxr,?_⟩
    simpa only [cubicSymbol_mul_upper hx,cubicSymbol_pow_upper hx,
      cubicSymbol_cube_of_isCoprime hx c hxc,mul_one] using hne
  · exact cubicNumeratorChar_mul_cube_ne_one hpub hr hc

end CubicFirstMoment

end

end OAI
