import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeRootPairingL2
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeRootBruhatMass
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeRootWeylFixed

namespace OAI

/-! Distinct fractional translates of the original global space are
orthogonal, and all are orthogonal to its Weyl translate. -/
noncomputable section
namespace CubicFirstMoment

theorem cubicThetaPrimeRootWeyl_translate_pair_zero {p : Eisenstein} (hp : primaryPrime p)
    (r : Residues p) (u v : cubicThetaAutomorphicL2) :
    inner ℂ (cubicThetaPrimeRootWeylL2 hp (cubicThetaPrimeRootLiftL2 hp u))
      (cubicThetaPrimeRootResidueL2 hp r (cubicThetaPrimeRootLiftL2 hp v))=0 := by
  calc
    _ = inner ℂ (cubicThetaPrimeRootResidueL2 hp r
        (cubicThetaPrimeRootWeylL2 hp (cubicThetaPrimeRootLiftL2 hp u)))
        (cubicThetaPrimeRootResidueL2 hp r (cubicThetaPrimeRootLiftL2 hp v)) := by
          rw [cubicThetaPrimeRootWeyl_lift_translate]
    _ = inner ℂ (cubicThetaPrimeRootWeylL2 hp (cubicThetaPrimeRootLiftL2 hp u))
        (cubicThetaPrimeRootLiftL2 hp v) := (cubicThetaPrimeRootResidueL2 hp r).inner_map_map _ _
    _ = 0 := (inner_eq_zero_symm (𝕜:=ℂ) (E:=cubicThetaPrimeRootAutomorphicL2 hp)).mp
      (cubicThetaPrimeRootLiftWeyl_orthogonal hp v u)

theorem cubicThetaPrimeRootLift_translate_pair_zero {p : Eisenstein} (hp : primaryPrime p)
    (r : Residues p) (hr : r≠0) (u v : cubicThetaAutomorphicL2) :
    inner ℂ (cubicThetaPrimeRootLiftL2 hp u)
      (cubicThetaPrimeRootResidueL2 hp r (cubicThetaPrimeRootLiftL2 hp v))=0 := by
  classical
  let : (modulus p).IsPrime := (Ideal.span_singleton_prime hp.2.ne_zero).mpr hp.2
  let : Finite (Residues p) := finite_residues hp.2.ne_zero
  let : Fintype (Residues p) := Fintype.ofFinite _
  let : Field (Residues p) := Fintype.fieldOfDomain _
  calc
    _ = inner ℂ (cubicThetaPrimeRootWeylL2 hp (cubicThetaPrimeRootLiftL2 hp u))
        (cubicThetaPrimeRootWeylL2 hp
          (cubicThetaPrimeRootResidueL2 hp r (cubicThetaPrimeRootLiftL2 hp v))) :=
            ((cubicThetaPrimeRootWeylL2 hp).inner_map_map _ _).symm
    _ = inner ℂ (cubicThetaPrimeRootWeylL2 hp (cubicThetaPrimeRootLiftL2 hp u))
        ((cubicSymbol p 3*cubicResidueChar p hp r) •
          cubicThetaPrimeRootResidueL2 hp (-cubicThetaPrimeRootReciprocal p r)
            (cubicThetaPrimeRootLiftL2 hp (cubicThetaInversionMass v))) := by
              rw [cubicThetaPrimeRootWeyl_mass_bruhat hp r (isUnit_iff_ne_zero.mpr hr)]
    _ = 0 := by
      rw [inner_smul_right (𝕜:=ℂ) (E:=cubicThetaPrimeRootAutomorphicL2 hp),
        cubicThetaPrimeRootWeyl_translate_pair_zero,mul_zero]

theorem cubicThetaPrimeRootOrbit_pair_zero {p : Eisenstein} (hp : primaryPrime p)
    (r s : Residues p) (hrs : r≠s) (u v : cubicThetaAutomorphicL2) :
    inner ℂ (cubicThetaPrimeRootResidueL2 hp r (cubicThetaPrimeRootLiftL2 hp u))
      (cubicThetaPrimeRootResidueL2 hp s (cubicThetaPrimeRootLiftL2 hp v))=0 := by
  have he : r+(s-r)=s := by abel
  calc
    _ = inner ℂ (cubicThetaPrimeRootResidueL2 hp r (cubicThetaPrimeRootLiftL2 hp u))
        (cubicThetaPrimeRootResidueL2 hp r
          (cubicThetaPrimeRootResidueL2 hp (s-r) (cubicThetaPrimeRootLiftL2 hp v))) := by
            rw [←cubicThetaPrimeRootResidueL2_add,he]
    _ = inner ℂ (cubicThetaPrimeRootLiftL2 hp u)
        (cubicThetaPrimeRootResidueL2 hp (s-r) (cubicThetaPrimeRootLiftL2 hp v)) :=
          (cubicThetaPrimeRootResidueL2 hp r).inner_map_map _ _
    _ = 0 := cubicThetaPrimeRootLift_translate_pair_zero hp (s-r) (sub_ne_zero.mpr hrs.symm) u v

end CubicFirstMoment

end

end OAI
