import OAI.NumberTheory.CubicMoment.Theta.CubicThetaNineDualPhase
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaRamanujanProduct

namespace OAI

/-! The inverse residues arising from determinant-one cusp lifts permute
the actual unit group. No distribution or cancellation estimate is assumed. -/
noncomputable section
open scoped BigOperators MatrixGroups
namespace CubicFirstMoment
attribute [local instance] Classical.propDecidable

def cubicThetaNineConductorUnit (r : Eisenstein) (hr : primary r) : (Residues r)ˣ :=
  (residue_isUnit_of_isCoprime
    ((cubicTheta_coprime_nine hr).mul_right ((primary_coprime_lambda hr).pow_right (n:=3)))).unit

lemma cubicThetaNineConductorUnit_val (r : Eisenstein) (hr : primary r) :
    (cubicThetaNineConductorUnit r hr:Residues r)=
      Ideal.Quotient.mk (modulus r) (9*lambdaE^3) :=
  (residue_isUnit_of_isCoprime
    ((cubicTheta_coprime_nine hr).mul_right ((primary_coprime_lambda hr).pow_right (n:=3)))).unit_spec

lemma cubicThetaUnitRepresentative_coprime (r : Eisenstein) (u : (Residues r)ˣ) :
    IsCoprime r (residueRepresentative r u) := by
  apply isCoprime_of_residue_isUnit
  rw [residueRepresentative_spec]
  exact u.isUnit

def cubicThetaNineUnitInverse (r : Eisenstein) (hr : primary r) (u : (Residues r)ˣ) : Eisenstein :=
  Classical.choose (cubicThetaNineGaussMatrix_nine r hr (residueRepresentative r u)
    (cubicThetaUnitRepresentative_coprime r u))

lemma cubicThetaNineUnitInverse_spec (r : Eisenstein) (hr : primary r) (u : (Residues r)ˣ) :
    cubicThetaNineGaussMatrix r hr (residueRepresentative r u)
      (cubicThetaUnitRepresentative_coprime r u) 1 1=9*cubicThetaNineUnitInverse r hr u :=
  Classical.choose_spec (cubicThetaNineGaussMatrix_nine r hr (residueRepresentative r u)
    (cubicThetaUnitRepresentative_coprime r u))

lemma cubicThetaNineUnitInverse_residue (r : Eisenstein) (hr : primary r) (u : (Residues r)ˣ) :
    Ideal.Quotient.mk (modulus r) (cubicThetaNineUnitInverse r hr u)=
      (((cubicThetaNineConductorUnit r hr*u)⁻¹ : (Residues r)ˣ):Residues r) := by
  let A := cubicThetaNineConductorUnit r hr
  let δ := cubicThetaNineUnitInverse r hr u
  have hd := cubicThetaNineGaussMatrix_inverse r hr (residueRepresentative r u)
    (cubicThetaUnitRepresentative_coprime r u) δ (cubicThetaNineUnitInverse_spec r hr u)
  have he := residue_eq_of_dvd_sub hd
  have hp : ((A*u:(Residues r)ˣ):Residues r)*Ideal.Quotient.mk (modulus r) δ=1 := by
    rw [Units.val_mul,cubicThetaNineConductorUnit_val]
    simpa only [map_mul,map_pow,map_one,residueRepresentative_spec,mul_assoc] using he
  have hi : (((A*u)⁻¹:(Residues r)ˣ):Residues r)*((A*u:(Residues r)ˣ):Residues r)=1 :=
    (A*u).inv_mul
  change Ideal.Quotient.mk (modulus r) δ=_
  calc
    _ = 1*Ideal.Quotient.mk (modulus r) δ := (one_mul _).symm
    _ = ((((A*u)⁻¹:(Residues r)ˣ):Residues r)*((A*u:(Residues r)ˣ):Residues r))*
        Ideal.Quotient.mk (modulus r) δ := by rw [hi]
    _ = (((A*u)⁻¹:(Residues r)ˣ):Residues r)*
        (((A*u:(Residues r)ˣ):Residues r)*Ideal.Quotient.mk (modulus r) δ) := mul_assoc _ _ _
    _ = _ := by rw [hp,mul_one]

theorem cubicThetaNineUnitInverse_average (r : Eisenstein) (hr : primary r)
    [Fintype (Residues r)] (n : Eisenstein) :
    (∑ u : (Residues r)ˣ,additivePhase r (-n*cubicThetaNineUnitInverse r hr u))=
      cubicThetaRamanujan r n := by
  let A := cubicThetaNineConductorUnit r hr
  let e : Equiv.Perm ((Residues r)ˣ) :=
    ((Equiv.mulLeft A).trans (Equiv.inv _)).trans (Equiv.neg _)
  have he (u : (Residues r)ˣ) : (e u:Residues r)=
      -((((A*u)⁻¹:(Residues r)ˣ):Residues r)) := rfl
  have ht (u : (Residues r)ˣ) :
      additivePhase r (-n*cubicThetaNineUnitInverse r hr u)=
        additivePhase r (n*residueRepresentative r (e u)) := by
    apply additivePhase_congr (primary_ne_zero hr)
    rw [map_mul,map_mul,residueRepresentative_spec,he,map_neg,
      cubicThetaNineUnitInverse_residue]
    ring
  simp_rw [ht]
  calc
    _ = ∑ u : (Residues r)ˣ, additivePhase r (n*residueRepresentative r u) :=
      Equiv.sum_comp e (fun u : (Residues r)ˣ => additivePhase r (n*residueRepresentative r u))
    _ = _ := (cubicThetaRamanujan_units hr n).symm

end CubicFirstMoment

end

end OAI
