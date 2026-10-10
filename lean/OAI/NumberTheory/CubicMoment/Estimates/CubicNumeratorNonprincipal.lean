import OAI.NumberTheory.CubicMoment.Estimates.CubicNumeratorOrder
import OAI.NumberTheory.CubicMoment.Estimates.PrimaryCharacterNonprincipal

namespace OAI

/-! Nontrivial cubic numerator characters in the squarefree primary case,
using the mixed-character Fourier witness and reciprocity. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicNumeratorChar_squarefree_nonprincipal (hpub : CubicSupplementaryPeriodicity)
    {v : Eisenstein} (hv : primary v) (hvs : Squarefree v) (hvu : ¬ IsUnit v) :
    cubicNumeratorChar hpub v (primary_ne_zero hv) ≠ 1 := by
  have hnu : ¬ IsUnit (v*1) := by simpa only [mul_one] using hvu
  obtain ⟨x,hx,hcop,hne⟩ := mixedCubic_nonprincipal hv primary_one hvs
    squarefree_one isCoprime_one_right hnu
  have hcopv : IsCoprime v x := by simpa only [mul_one] using hcop
  have hcop9 : IsCoprime (9:Eisenstein) x := by
    convert ((primary_coprime_three hx).symm.pow_left (m := 2)) using 1
    norm_num
  apply (cubicNumeratorChar_ne_one_iff hpub v (primary_ne_zero hv)).mpr
  refine ⟨x,hx,hcop9.mul_left hcopv,?_⟩
  have hne' : cubicSymbol v x ≠ 1 := by
    simpa only [mixedCubic,cubicSymbol_one_lower,star_one,mul_one] using hne
  rwa [cubic_reciprocity hx hv]

lemma cubicNumeratorChar_squarefree_nonreal (hpub : CubicSupplementaryPeriodicity)
    {v : Eisenstein} (hv : primary v) (hvs : Squarefree v) (hvu : ¬ IsUnit v) :
    star (cubicNumeratorChar hpub v (primary_ne_zero hv)) ≠
      cubicNumeratorChar hpub v (primary_ne_zero hv) :=
  cubicNumeratorChar_not_self_conjugate hpub v (primary_ne_zero hv)
    (cubicNumeratorChar_squarefree_nonprincipal hpub hv hvs hvu)

end CubicFirstMoment

end

end OAI
