import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeCosetPermutation
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeSectionNorm

namespace OAI

/-! The literal finite trace from the prime cover to the original
cubic automorphy character. No normality of the covering subgroup is required. -/
noncomputable section
namespace CubicFirstMoment

local instance primeTrace_fintype {p : Eisenstein} (hp : primaryPrime p) :
    Fintype (cubicThetaPrimeTransversal hp) := Fintype.ofFinite _

def cubicThetaPrimeTraceTerm {p : Eisenstein} (hp : primaryPrime p)
    (F : cubicThetaPrimeSections hp) (g : cubicThetaPrincipalGroup) (x : CubicThetaPoint) : ℂ :=
  star (cubicThetaKubotaValue g)*F.val (g • x)

lemma cubicThetaPrimeTraceTerm_left {p : Eisenstein} (hp : primaryPrime p)
    (F : cubicThetaPrimeSections hp) (h : cubicThetaPrimeCoverGroup hp)
    (g : cubicThetaPrincipalGroup) (x : CubicThetaPoint) :
    cubicThetaPrimeTraceTerm hp F (h.val*g) x=cubicThetaPrimeTraceTerm hp F g x := by
  have hu : star (cubicThetaKubotaValue h.val)*cubicThetaKubotaValue h.val=1 := by
    rw [mul_comm,Complex.star_def,Complex.mul_conj',cubicThetaKubotaValue_norm]
    norm_num
  unfold cubicThetaPrimeTraceTerm
  rw [mul_smul]
  change star (cubicThetaKubotaValue (h.val*g))*F.val (h • (g • x))=_
  rw [cubicThetaPrimeSection_property hp F h,cubicThetaKubotaValue_mul,star_mul]
  calc
    _ = (star (cubicThetaKubotaValue h.val)*cubicThetaKubotaValue h.val)*
      (star (cubicThetaKubotaValue g)*F.val (g • x)) := by ring
    _ = _ := by rw [hu,one_mul]

lemma cubicThetaPrimeTraceTerm_translate {p : Eisenstein} (hp : primaryPrime p)
    (F : cubicThetaPrimeSections hp) (g h : cubicThetaPrincipalGroup) (x : CubicThetaPoint) :
    cubicThetaPrimeTraceTerm hp F g (h • x)=
      cubicThetaKubotaValue h*cubicThetaPrimeTraceTerm hp F (g*h) x := by
  have hu : cubicThetaKubotaValue h*star (cubicThetaKubotaValue h)=1 := by
    rw [Complex.star_def,Complex.mul_conj',cubicThetaKubotaValue_norm]
    norm_num
  calc
    _ = (cubicThetaKubotaValue h*star (cubicThetaKubotaValue h))*
      cubicThetaPrimeTraceTerm hp F g (h • x) := by rw [hu,one_mul]
    _ = _ := by
      simp only [cubicThetaPrimeTraceTerm,cubicThetaKubotaValue_mul,star_mul,mul_smul]
      ring

lemma cubicThetaPrimeTraceTerm_permute {p : Eisenstein} (hp : primaryPrime p)
    (F : cubicThetaPrimeSections hp) (g : cubicThetaPrincipalGroup)
    (t : cubicThetaPrimeTransversal hp) (x : CubicThetaPoint) :
    cubicThetaPrimeTraceTerm hp F (t.val*g) x=
      cubicThetaPrimeTraceTerm hp F (cubicThetaPrimeCosetPermutation hp g t).val x := by
  rw [←cubicThetaPrimeCosetPermutation_factor hp g t,cubicThetaPrimeTraceTerm_left]

def cubicThetaPrimeTraceSection {p : Eisenstein} (hp : primaryPrime p)
    (F : cubicThetaPrimeSections hp) : CubicThetaSection :=
  ⟨⟨fun x => ∑ t : cubicThetaPrimeTransversal hp, cubicThetaPrimeTraceTerm hp F t.val x,
    by
      apply continuous_finsetSum
      intro t _
      exact continuous_const.mul (F.val.continuous.comp (continuous_const_smul t.val))⟩,by
    intro g x
    change (∑ t : cubicThetaPrimeTransversal hp, cubicThetaPrimeTraceTerm hp F t.val (g • x))=
      cubicThetaKubotaValue g*(∑ t : cubicThetaPrimeTransversal hp, cubicThetaPrimeTraceTerm hp F t.val x)
    simp_rw [cubicThetaPrimeTraceTerm_translate,cubicThetaPrimeTraceTerm_permute]
    rw [←Finset.mul_sum]
    congr 1
    exact Equiv.sum_comp (cubicThetaPrimeCosetPermutation hp g)
      (fun t => cubicThetaPrimeTraceTerm hp F t.val x)⟩

lemma cubicThetaPrimeTraceSection_restrict {p : Eisenstein} (hp : primaryPrime p)
    (F : CubicThetaSection) (x : CubicThetaPoint) :
    (cubicThetaPrimeTraceSection hp (cubicThetaPrimeSectionRestrict hp F)).val x=
      ((cubicThetaPrimeCoverGroup hp).index:ℂ)*F.val x := by
  change (∑ t : cubicThetaPrimeTransversal hp,
    star (cubicThetaKubotaValue t.val)*F.val (t.val • x))=_
  have ht (t : cubicThetaPrimeTransversal hp) :
      star (cubicThetaKubotaValue t.val)*F.val (t.val • x)=F.val x := by
    rw [F.property,←mul_assoc]
    have hu : star (cubicThetaKubotaValue t.val)*cubicThetaKubotaValue t.val=1 := by
      rw [mul_comm,Complex.star_def,Complex.mul_conj',cubicThetaKubotaValue_norm]
      norm_num
    rw [hu,one_mul]
  simp_rw [ht]
  rw [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,
    ←Nat.card_eq_fintype_card,(cubicThetaPrimeTransversal_complement hp).card_right]

end CubicFirstMoment

end

end OAI
