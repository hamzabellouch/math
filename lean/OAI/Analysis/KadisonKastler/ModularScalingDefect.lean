import OAI.Analysis.KadisonKastler.ModularRightAction

namespace OAI

/-! # Adjoint symmetry of the modular scaling defect -/

namespace KadisonKastler

open Filter
open scoped Topology

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] {M : VonNeumannAlgebra H} {Ω : H}

namespace ModularConjugationData

variable (d : ModularConjugationData M Ω)

theorem rightAction_adjoint_defect (v : Algebra M) (t : ℝ) :
    (t : ℂ) • (star v).val Ω-d.rightAction (star v) Ω =
      -d.conjugation (v.val Ω-(t : ℂ) • d.rightAction v Ω) := by
  simp only [rightAction,conjugationOperator_apply,d.fixes_vector,
    StarMemClass.coe_star,star_star,map_sub,d.conjugation.map_smulₛₗ,
    Complex.conj_ofReal]
  rw [d.involutive (star v.val Ω)]
  abel

theorem rightAction_adjoint_defect_tendsto (v : ℕ → Algebra M) (t : ℝ)
    (hv : Tendsto (fun n => (v n).val Ω-(t : ℂ) • d.rightAction (v n) Ω)
      atTop (𝓝 0)) :
    Tendsto (fun n => (t : ℂ) • (star (v n)).val Ω-d.rightAction (star (v n)) Ω)
      atTop (𝓝 0) := by
  have ht := (d.conjugation.continuous.continuousAt.tendsto.comp hv).neg
  simpa only [map_zero,neg_zero,d.rightAction_adjoint_defect,Function.comp_def] using ht

end ModularConjugationData

end

end KadisonKastler

end OAI
