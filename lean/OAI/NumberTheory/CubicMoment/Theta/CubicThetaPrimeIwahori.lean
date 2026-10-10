import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeResidueImage
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaKubotaCharacter
import Mathlib.GroupTheory.Index

namespace OAI

/-! The actual finite-index subgroup and cubic diagonal character needed
for the unramified local correspondence. All data come from reduction of
the principal arithmetic group; no local representation input is assumed. -/
noncomputable section
open scoped MatrixGroups
namespace CubicFirstMoment

def cubicThetaPrimeIwahori (p : Eisenstein) : Subgroup cubicThetaPrincipalGroup where
  carrier := {g | p∣g.val 1 0}
  one_mem' := by simp
  mul_mem' := by
    intro g h hg hh
    change p∣(g.val*h.val) 1 0
    simp only [Matrix.SpecialLinearGroup.coe_mul,Matrix.mul_apply,Fin.sum_univ_two]
    exact dvd_add (dvd_mul_of_dvd_left hg _) (dvd_mul_of_dvd_right hh _)
  inv_mem' := by
    intro g hg
    change p∣(g.val⁻¹) 1 0
    simpa [Matrix.SpecialLinearGroup.coe_inv,Matrix.adjugate_fin_two] using dvd_neg.mpr hg

def cubicThetaPrimeReduction (p : Eisenstein) :
    cubicThetaPrincipalGroup →* SL(2,Residues p) :=
  (Matrix.SpecialLinearGroup.map (Ideal.Quotient.mk (modulus p))).comp
    cubicThetaPrincipalGroup.subtype

lemma cubicThetaPrimeReduction_ker_le (p : Eisenstein) :
    (cubicThetaPrimeReduction p).ker≤cubicThetaPrimeIwahori p := by
  intro g hg
  have he := congrArg (fun A : SL(2,Residues p) => A 1 0) hg
  change Ideal.Quotient.mk (modulus p) (g.val 1 0)=0 at he
  exact Ideal.mem_span_singleton.mp (Ideal.Quotient.eq_zero_iff_mem.mp he)

theorem cubicThetaPrimeIwahori_finiteIndex {p : Eisenstein} (hp : p≠0) :
    (cubicThetaPrimeIwahori p).FiniteIndex := by
  let : Finite (Residues p) := finite_residues hp
  let : Finite (cubicThetaPrimeReduction p).range := inferInstance
  let : (cubicThetaPrimeReduction p).ker.FiniteIndex := inferInstance
  exact Subgroup.finiteIndex_of_le (cubicThetaPrimeReduction_ker_le p)

lemma cubicThetaPrimeIwahori_diagonal_coprime {p : Eisenstein}
    (hp : primaryPrime p) (g : cubicThetaPrimeIwahori p) :
    IsCoprime p (g.val.val 0 0) := by
  apply hp.2.coprime_iff_not_dvd.mpr
  intro hd
  exact hp.2.not_isUnit ((cubicThetaPrincipalGroup_column_coprime g.val).isRelPrime hd g.property)

def cubicThetaPrimeIwahoriCharacter (p : Eisenstein) (hp : primaryPrime p) :
    cubicThetaPrimeIwahori p →* ℂ where
  toFun g := cubicSymbol p (g.val.val 0 0)
  map_one' := by
    change cubicSymbol p 1=1
    simpa only [pow_zero] using cubicSymbol_pow_upper hp.1 1 0
  map_mul' g h := by
    change cubicSymbol p ((g.val.val*h.val.val) 0 0)=
      cubicSymbol p (g.val.val 0 0)*cubicSymbol p (h.val.val 0 0)
    have he : p∣(g.val.val*h.val.val) 0 0-(g.val.val 0 0)*(h.val.val 0 0) := by
      simp only [Matrix.SpecialLinearGroup.coe_mul,Matrix.mul_apply,Fin.sum_univ_two,add_sub_cancel_left]
      exact dvd_mul_of_dvd_right h.property _
    rw [cubicSymbol_congr (residue_eq_of_dvd_sub he),cubicSymbol_mul_upper hp.1]

lemma cubicThetaPrimeIwahoriCharacter_norm {p : Eisenstein} (hp : primaryPrime p)
    (g : cubicThetaPrimeIwahori p) : ‖cubicThetaPrimeIwahoriCharacter p hp g‖=1 :=
  norm_cubicSymbol_of_isCoprime hp.1 (cubicThetaPrimeIwahori_diagonal_coprime hp g)

lemma cubicThetaPrimeIwahoriCharacter_cube {p : Eisenstein} (hp : primaryPrime p)
    (g : cubicThetaPrimeIwahori p) : (cubicThetaPrimeIwahoriCharacter p hp g)^3=1 :=
  cubicSymbol_cube_of_isCoprime hp.1 _ (cubicThetaPrimeIwahori_diagonal_coprime hp g)

end CubicFirstMoment

end

end OAI
