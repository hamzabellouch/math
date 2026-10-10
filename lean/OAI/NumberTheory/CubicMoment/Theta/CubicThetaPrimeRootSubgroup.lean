import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeConjugation

namespace OAI

/-! A finite-index arithmetic subgroup on which the fractional upper-root
translations can act. The diagonal congruence is retained explicitly. -/
noncomputable section
open scoped MatrixGroups
namespace CubicFirstMoment

def cubicThetaPrimeRootSubgroup (p : Eisenstein) : Subgroup cubicThetaPrincipalGroup where
  carrier := {g | p^2∣g.val 1 0 ∧ p∣g.val 0 0-g.val 1 1}
  one_mem' := by simp
  mul_mem' := by
    intro g h hg hh
    refine ⟨(cubicThetaPrimeIwahori (p^2)).mul_mem hg.1 hh.1,?_⟩
    have hgc : p∣g.val 1 0 := (dvd_pow_self p (by decide : 2≠0)).trans hg.1
    have hhc : p∣h.val 1 0 := (dvd_pow_self p (by decide : 2≠0)).trans hh.1
    change p∣(g.val*h.val) 0 0-(g.val*h.val) 1 1
    simp only [Matrix.SpecialLinearGroup.coe_mul,Matrix.mul_apply,Fin.sum_univ_two]
    rw [show (g.val 0 0*h.val 0 0+g.val 0 1*h.val 1 0)-
        (g.val 1 0*h.val 0 1+g.val 1 1*h.val 1 1)=
        g.val 0 0*(h.val 0 0-h.val 1 1)+h.val 1 1*(g.val 0 0-g.val 1 1)+
          g.val 0 1*h.val 1 0-g.val 1 0*h.val 0 1 by ring]
    exact dvd_sub (dvd_add (dvd_add (dvd_mul_of_dvd_right hh.2 _)
      (dvd_mul_of_dvd_right hg.2 _)) (dvd_mul_of_dvd_right hhc _)) (dvd_mul_of_dvd_left hgc _)
  inv_mem' := by
    intro g hg
    refine ⟨(cubicThetaPrimeIwahori (p^2)).inv_mem hg.1,?_⟩
    change p∣(g.val⁻¹) 0 0-(g.val⁻¹) 1 1
    simpa [Matrix.SpecialLinearGroup.coe_inv,Matrix.adjugate_fin_two,neg_sub] using dvd_neg.mpr hg.2


lemma cubicThetaPrimeRootSubgroup_ker_le (p : Eisenstein) :
    (cubicThetaPrimeReduction (p^2)).ker≤cubicThetaPrimeRootSubgroup p := by
  intro g hg
  refine ⟨cubicThetaPrimeReduction_ker_le (p^2) hg,?_⟩
  have ha := congrArg (fun A : SL(2,Residues (p^2)) => A 0 0) hg
  have hd := congrArg (fun A : SL(2,Residues (p^2)) => A 1 1) hg
  change Ideal.Quotient.mk (modulus (p^2)) (g.val 0 0)=1 at ha
  change Ideal.Quotient.mk (modulus (p^2)) (g.val 1 1)=1 at hd
  have hz : Ideal.Quotient.mk (modulus (p^2)) (g.val 0 0-g.val 1 1)=0 := by
    rw [map_sub,ha,hd,sub_self]
  exact (dvd_pow_self p (by decide : 2≠0)).trans
    (Ideal.mem_span_singleton.mp (Ideal.Quotient.eq_zero_iff_mem.mp hz))

theorem cubicThetaPrimeRootSubgroup_finiteIndex {p : Eisenstein} (hp : p≠0) :
    (cubicThetaPrimeRootSubgroup p).FiniteIndex := by
  let : Finite (Residues (p^2)) := finite_residues (pow_ne_zero 2 hp)
  let : Finite (cubicThetaPrimeReduction (p^2)).range := inferInstance
  let : (cubicThetaPrimeReduction (p^2)).ker.FiniteIndex := inferInstance
  exact Subgroup.finiteIndex_of_le (cubicThetaPrimeRootSubgroup_ker_le p)

end CubicFirstMoment

end

end OAI
