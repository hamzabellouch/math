import OAI.Analysis.KadisonKastler.ModularConjugationData
import Mathlib.Analysis.InnerProductSpace.Adjoint

namespace OAI

/-! # The bounded right action in a modular representation -/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] {M : VonNeumannAlgebra H} {Ω : H}

namespace ModularConjugationData

variable (d : ModularConjugationData M Ω)

def rightAction (a : Algebra M) : H →L[ℂ] H :=
  conjugationOperator d.conjugation (star a.val)

theorem rightAction_mem (a : Algebra M) : d.rightAction a ∈ M.commutant :=
  d.right_mem (R := M) le_rfl (star a)

theorem rightAction_commute (a b : Algebra M) :
    a.val * d.rightAction b = d.rightAction b * a.val :=
  VonNeumannAlgebra.mem_commutant_iff.mp (d.rightAction_mem b) a.val a.property

theorem rightAction_mul (a b : Algebra M) :
    d.rightAction (a*b) = d.rightAction b * d.rightAction a := by
  change conjugationOperator d.conjugation (star (a.val*b.val)) = _
  rw [star_mul,conjugationOperator_mul d.conjugation d.involutive]
  rfl

theorem rightAction_one : d.rightAction (1 : Algebra M) = 1 := by
  change conjugationOperator d.conjugation (star (1 : H →L[ℂ] H)) = _
  rw [star_one,conjugationOperator_one d.conjugation d.involutive]

theorem rightAction_star (a : Algebra M) :
    d.rightAction (star a) = star (d.rightAction a) := by
  exact conjugationOperator_star d.conjugation d.involutive (star a.val)

theorem rightAction_norm (a : Algebra M) : ‖d.rightAction a‖ = ‖a‖ := by
  rw [rightAction,norm_conjugationOperator d.conjugation d.involutive,norm_star]
  rfl

theorem rightAction_isometry (v : Algebra M) (hv : v*star v=1) :
    Isometry (d.rightAction v) := by
  apply (d.rightAction v).isometry_iff_adjoint_comp_self.mpr
  change star (d.rightAction v)*d.rightAction v=1
  rw [← d.rightAction_star,← d.rightAction_mul,hv,d.rightAction_one]

theorem rightAction_norm_map (v : Algebra M) (hv : v*star v=1) (η : H) :
    ‖d.rightAction v η‖ = ‖η‖ := by
  exact (d.rightAction_isometry v hv).norm_map_of_map_zero (map_zero _) η

end ModularConjugationData

end

end KadisonKastler

end OAI
