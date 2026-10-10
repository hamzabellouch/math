import OAI.NumberTheory.CubicMoment.Theta.CubicThetaTwistFourier
import OAI.NumberTheory.CubicMoment.Estimates.PrimaryHeckeCharacter
import OAI.NumberTheory.CubicGram.MixedPoisson

namespace OAI

/-! The finite Ramanujan sum in the trace normalization of the actual
cubic theta series. Its weight is the cube of the cubic residue character. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment
attribute [local instance] Classical.propDecidable

lemma cubicThetaSymbol_cube_indicator {r : Eisenstein} (hr : primary r) (x : Eisenstein) :
    cubicSymbol r x^3=(if IsCoprime r x then 1 else 0) := by
  by_cases hx : IsCoprime r x
  · rw [ite_eq_left hx,cubicSymbol_cube_of_isCoprime hr x hx]
  · rw [ite_eq_right hx,cubicSymbol_eq_zero_of_not_isCoprime hr hx]
    norm_num

def cubicThetaRamanujan (r h : Eisenstein) : ℂ :=
  ∑' x : Residues r,cubicSymbol r (residueRepresentative r x)^3*
    additivePhase r (h*residueRepresentative r x)

lemma cubicThetaRamanujan_prime {p : Eisenstein} (hp : primaryPrime p) (h : Eisenstein) :
    cubicThetaRamanujan p h=if p∣h then (norm p:ℂ)-1 else -1 := by
  let : (modulus p).IsPrime := (Ideal.span_singleton_prime hp.2.ne_zero).mpr hp.2
  let : Finite (Residues p) := finite_residues hp.2.ne_zero
  let : Fintype (Residues p) := Fintype.ofFinite _
  let : Field (Residues p) := Fintype.fieldOfDomain _
  let χ := cubicThetaResidueChar p hp.2.ne_zero
  let a := Ideal.Quotient.mk (modulus p) h
  have ha : a=0 ↔ p∣h := by
    rw [Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mem_span_singleton
  have hc (x : Residues p) : IsCoprime p (residueRepresentative p x) ↔ x≠0 := by
    constructor
    · intro hx
      have hu := residue_isUnit_of_isCoprime hx
      rw [residueRepresentative_spec,isUnit_iff_ne_zero] at hu
      exact hu
    · intro hx
      apply isCoprime_of_residue_isUnit
      rw [residueRepresentative_spec]
      exact isUnit_iff_ne_zero.mpr hx
  have he (x : Residues p) : additivePhase p (h*residueRepresentative p x)=χ (a*x) := by
    rw [additivePhase_fourierChar]
    have hh := cubicThetaResidueChar_mk p hp.2.ne_zero (h*residueRepresentative p x)
    rw [map_mul,residueRepresentative_spec] at hh
    exact hh.symm
  rw [cubicThetaRamanujan,tsum_fintype]
  simp_rw [cubicThetaSymbol_cube_indicator hp.1,hc,he]
  have hs : (∑ x : Residues p,(if x≠0 then (1:ℂ) else 0)*χ (a*x))=
      (∑ x : Residues p,χ (a*x))-1 := by
    rw [←Finset.sum_erase_add _ _ (Finset.mem_univ (0:Residues p))]
    simp only [ne_eq,not_true_eq_false,ite_false,mul_zero,zero_mul,χ.map_zero_eq_one,add_zero]
    rw [eq_sub_iff_add_eq]
    rw [←Finset.sum_erase_add _ _ (Finset.mem_univ (0:Residues p))]
    simp only [mul_zero,χ.map_zero_eq_one]
    congr 1
    apply Finset.sum_congr rfl
    intro x hx
    rw [ite_eq_left (Finset.ne_of_mem_erase hx),one_mul]
  rw [hs]
  simp_rw [mul_comm a]
  rw [AddChar.sum_mulShift a (cubicThetaResidueChar_primitive hp.1),ha]
  have hn : (Fintype.card (Residues p):ℂ)=(norm p:ℂ) := by
    rw [←Nat.card_eq_fintype_card,residues_card hp.2.ne_zero]
    exact_mod_cast normNat_cast p
  split_ifs <;> simp_all

lemma cubicThetaRamanujan_one (h : Eisenstein) : cubicThetaRamanujan 1 h=1 := by
  have he := frequencyGauss_one h
  have hn : norm (1:Eisenstein)=1 := by norm_num [norm]
  rw [frequencyGauss,hn,Real.sqrt_one,Complex.ofReal_one,inv_one,one_mul] at he
  simpa only [frequencyGauss,cubicThetaRamanujan,cubicSymbol_one_lower,one_pow,one_mul,
    norm_one,Real.sqrt_one,Complex.ofReal_one,inv_one] using he

lemma cubicThetaRamanujan_mul {a b : Eisenstein} (ha : primary a) (hb : primary b)
    (hab : IsCoprime a b) (h : Eisenstein) :
    cubicThetaRamanujan (a*b) h=cubicThetaRamanujan a h*cubicThetaRamanujan b h := by
  let : Finite (Residues a) := finite_residues (primary_ne_zero ha)
  let : Finite (Residues b) := finite_residues (primary_ne_zero hb)
  let : Finite (Residues (a*b)) := finite_residues (mul_ne_zero (primary_ne_zero ha) (primary_ne_zero hb))
  let : Fintype (Residues a) := Fintype.ofFinite _
  let : Fintype (Residues b) := Fintype.ofFinite _
  let : Fintype (Residues (a*b)) := Fintype.ofFinite _
  let e := Equiv.ofBijective (residueMix a b)
    (residueMix_bijective (primary_ne_zero ha) (primary_ne_zero hb) hab)
  let f (q : Eisenstein) (x : Residues q) : ℂ :=
    cubicSymbol q (residueRepresentative q x)^3*additivePhase q (h*residueRepresentative q x)
  have ht (v : Residues a × Residues b) : f (a*b) (e v)=f a v.1*f b v.2 := by
    have heq : Ideal.Quotient.mk (modulus (a*b)) (residueRepresentative (a*b) (e v))=
        Ideal.Quotient.mk (modulus (a*b))
          (b*residueRepresentative a v.1+a*residueRepresentative b v.2) :=
      residueRepresentative_spec _ _
    have heqh : Ideal.Quotient.mk (modulus (a*b)) (h*residueRepresentative (a*b) (e v))=
        Ideal.Quotient.mk (modulus (a*b))
          (h*(b*residueRepresentative a v.1+a*residueRepresentative b v.2)) := by
      rw [map_mul,map_mul,heq]
    dsimp only [f]
    rw [cubicSymbol_congr heq]
    rw [additivePhase_congr (mul_ne_zero (primary_ne_zero ha) (primary_ne_zero hb))
      heqh]
    rw [cubicSymbol_mix ha hb,mul_pow,mul_pow,mul_pow,
      cubicSymbol_cube_of_isCoprime ha b hab,cubicSymbol_cube_of_isCoprime hb a hab.symm]
    rw [show h*(b*residueRepresentative a v.1+a*residueRepresentative b v.2)=
      b*(h*residueRepresentative a v.1)+a*(h*residueRepresentative b v.2) by ring,
      additivePhase_mix (primary_ne_zero ha) (primary_ne_zero hb)]
    ring
  simp only [cubicThetaRamanujan,tsum_fintype]
  change (∑ x : Residues (a*b),f (a*b) x)=(∑ x,f a x)*(∑ x,f b x)
  rw [←Equiv.sum_comp e (f (a*b))]
  simp_rw [ht]
  rw [Fintype.sum_prod_type,←Finset.sum_mul_sum]

end CubicFirstMoment

end

end OAI
