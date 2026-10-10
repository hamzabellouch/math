import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeRootHorizontal

namespace OAI

/-! The root subgroup has central diagonal reduction modulo the prime.
Its diagonal cubic character is therefore trivial. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicThetaPrimeRoot_diagonal_square {p : Eisenstein} (_hp : primaryPrime p)
    (g : cubicThetaPrimeRootSubgroup p) : p∣(g.val.val 0 0)^2-1 := by
  have hc : p∣g.val.val 1 0 := (dvd_pow_self p (by decide : 2≠0)).trans g.property.1
  have he : (g.val.val 0 0)^2-1=
      g.val.val 0 0*(g.val.val 0 0-g.val.val 1 1)+g.val.val 0 1*g.val.val 1 0 := by
    linear_combination cubicThetaPrincipalGroup_det g.val
  rw [he]
  exact dvd_add (dvd_mul_of_dvd_right g.property.2 _) (dvd_mul_of_dvd_right hc _)

lemma cubicThetaPrimeRoot_diagonal_character {p : Eisenstein} (hp : primaryPrime p)
    (g : cubicThetaPrimeRootSubgroup p) : cubicSymbol p (g.val.val 0 0)=1 := by
  have h2 : (cubicSymbol p (g.val.val 0 0))^2=1 := by
    rw [←cubicSymbol_pow_upper hp.1,
      cubicSymbol_congr (residue_eq_of_dvd_sub (cubicThetaPrimeRoot_diagonal_square hp g))]
    simpa only [pow_zero] using cubicSymbol_pow_upper hp.1 1 0
  have h3 := cubicThetaPrimeIwahoriCharacter_cube hp (cubicThetaPrimeRootIwahori g)
  change (cubicSymbol p (g.val.val 0 0))^3=1 at h3
  calc
    _ = (cubicSymbol p (g.val.val 0 0))^2*cubicSymbol p (g.val.val 0 0) := by rw [h2,one_mul]
    _ = (cubicSymbol p (g.val.val 0 0))^3 := by ring
    _ = 1 := h3

def cubicThetaPrimeRootDilationIwahori {p : Eisenstein} (hp : primaryPrime p)
    (g : cubicThetaPrimeRootSubgroup p) : cubicThetaPrimeIwahori p :=
  ⟨cubicThetaPrimeConjugate hp.1 (cubicThetaPrimeRootIwahori g),by
    change p∣g.val.val 1 0/p
    rw [cubicThetaPrimeRoot_lower_single_division hp g]
    exact dvd_mul_right p _⟩

lemma cubicThetaPrimeRootDilation_kubota {p : Eisenstein} (hp : primaryPrime p)
    (g : cubicThetaPrimeRootSubgroup p) :
    cubicThetaKubotaValue (cubicThetaPrimeRootDilationIwahori hp g).val=
      cubicThetaKubotaValue g.val := by
  have he := cubicThetaPrimeConjugate_kubota hp (cubicThetaPrimeRootIwahori g)
  change cubicThetaKubotaValue g.val=cubicSymbol p (g.val.val 0 0)*
    cubicThetaKubotaValue (cubicThetaPrimeRootDilationIwahori hp g).val at he
  rw [cubicThetaPrimeRoot_diagonal_character hp g,one_mul] at he
  exact he.symm

end CubicFirstMoment

end

end OAI
