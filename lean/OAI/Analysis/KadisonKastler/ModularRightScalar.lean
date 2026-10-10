import OAI.Analysis.KadisonKastler.ModularRightAction

namespace OAI

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H} {Ω : H}

namespace ModularConjugationData

theorem rightAction_smul (d : ModularConjugationData M Ω) (c : ℂ) (a : Algebra M) :
    d.rightAction (c • a)=c • d.rightAction a := by
  change conjugationOperator d.conjugation (star (c • a.val)) = _
  rw [star_smul,conjugationOperator_smul,star_star]
  rfl

end ModularConjugationData

end

end KadisonKastler

end OAI
