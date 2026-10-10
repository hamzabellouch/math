import OAI.NumberTheory.CubicMoment.Estimates.CubicNumeratorNonprincipal
import OAI.NumberTheory.CubicMoment.Estimates.CoprimeResidueLift

namespace OAI

/-! The exact nonprincipal cubic numerator character for every primary
noncube, including numerators with repeated prime factors. -/
noncomputable section
namespace CubicFirstMoment

lemma mixedCubic_nonprincipal_avoiding {s t c : Eisenstein}
    (hs : primary s) (ht : primary t) (hss : Squarefree s) (hst : Squarefree t)
    (hst' : IsCoprime s t) (hnu : ¬ IsUnit (s*t)) (hc : c ≠ 0) :
    ∃ x : Eisenstein, primary x ∧ IsCoprime (s*t*c) x ∧ mixedCubic s t x ≠ 1 := by
  obtain ⟨y,hy,hycop,hyne⟩ := mixedCubic_nonprincipal hs ht hss hst hst' hnu
  have h3y : IsCoprime (3:Eisenstein) y := (primary_coprime_three hy).symm
  obtain ⟨x,hxy,hxcop⟩ := exists_coprime_residue_lift hc (h3y.mul_left hycop)
  have h3xy : (3:Eisenstein) ∣ x-y := (dvd_mul_right 3 (s*t)).trans hxy
  have hx : primary x := by
    change (3:Eisenstein) ∣ x-1
    convert dvd_add h3xy hy using 1
    ring
  have hsxy : s ∣ x-y := (show s ∣ 3*(s*t) from ⟨3*t,by ring⟩).trans hxy
  have htxy : t ∣ x-y := (show t ∣ 3*(s*t) from ⟨3*s,by ring⟩).trans hxy
  refine ⟨x,hx,?_,?_⟩
  · exact hxcop.of_isCoprime_of_dvd_left ⟨3,by ring⟩
  · simpa only [mixedCubic,cubicSymbol_congr (residue_eq_of_dvd_sub hsxy),
      cubicSymbol_congr (residue_eq_of_dvd_sub htxy)] using hyne

lemma cubicNumeratorChar_primary_noncube (hpub : CubicSupplementaryPeriodicity)
    {v : Eisenstein} (hv : primary v) (hvn : ¬∃ j : Eisenstein, j^3=v) :
    cubicNumeratorChar hpub v (primary_ne_zero hv) ≠ 1 := by
  obtain ⟨s,t,c,hs,ht,hc,hss,hst,hcop,hvst⟩ := primary_cube_decomposition hv
  have hnu : ¬ IsUnit (s*t) := by
    intro hu
    have hs1 := primary_unit_eq_one (isUnit_of_mul_isUnit_left hu) hs
    have ht1 := primary_unit_eq_one (isUnit_of_mul_isUnit_right hu) ht
    apply hvn
    exact ⟨c,by simpa only [hs1,ht1,one_pow,one_mul] using hvst.symm⟩
  obtain ⟨x,hx,hxcop,hxne⟩ := mixedCubic_nonprincipal_avoiding hs ht hss hst hcop
    hnu (primary_ne_zero hc)
  have hxc : IsCoprime x c := hxcop.of_mul_left_right.symm
  have hxv : IsCoprime v x := by
    rw [hvst]
    exact ((hxcop.of_mul_left_left.of_mul_left_left).mul_left
      ((hxcop.of_mul_left_left.of_mul_left_right).pow_left (m := 2))).mul_left
      (hxc.symm.pow_left (m := 3))
  have hx9 : IsCoprime (9:Eisenstein) x := by
    convert ((primary_coprime_three hx).symm.pow_left (m := 2)) using 1
    norm_num
  apply (cubicNumeratorChar_ne_one_iff hpub v (primary_ne_zero hv)).mpr
  refine ⟨x,hx,hx9.mul_left hxv,?_⟩
  have he : cubicSymbol x v = mixedCubic s t x := by
    rw [hvst,cubicSymbol_mul_upper hx,cubicSymbol_mul_upper hx,
      cubicSymbol_pow_upper hx,cubicSymbol_pow_upper hx,
      cubicSymbol_cube_of_isCoprime hx c hxc,mul_one,
      cubicSymbol_sq_eq_star hx,cubic_reciprocity hx hs,cubic_reciprocity hx ht]
    rfl
  rwa [he]

lemma cubicNumeratorChar_primary_eq_one_iff (hpub : CubicSupplementaryPeriodicity)
    {v : Eisenstein} (hv : primary v) :
    cubicNumeratorChar hpub v (primary_ne_zero hv) = 1 ↔ ∃ j : Eisenstein, j^3=v := by
  constructor
  · intro he
    by_contra hn
    exact cubicNumeratorChar_primary_noncube hpub hv hn he
  · exact cubicNumeratorChar_of_cube hpub v (primary_ne_zero hv)

end CubicFirstMoment

end

end OAI
