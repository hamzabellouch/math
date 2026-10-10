import OAI.Algebra.AuslanderReiten.Statement
import OAI.Algebra.AuslanderReiten.Complete.CompleteResolutionAllProjectives
import OAI.Algebra.AuslanderReiten.BaseChange.MainScalarExtension

namespace OAI

noncomputable section
open scoped TensorProduct
namespace ArExplicit.Statement
universe u v

theorem conclusions_iff {F R Z : Type u} [Field F] [Ring R] [Algebra F R]
    [AddCommGroup Z] [Module R Z] [Module F Z] [IsScalarTower F R Z] :
    ArExplicit.MainConclusions F R Z ↔ Conclusions F R Z := by
  constructor
  · rintro ⟨hR,hZ,hn,hg,hs,hr,hq,h4⟩
    exact ⟨hR,hZ,hn,hg.all_projective_targets,hs,hr,hq,h4⟩
  · rintro ⟨hR,hZ,hn,hg,hs,hr,hq,h4⟩
    exact ⟨hR,hZ,hn,ArExplicit.gorensteinProjective_iff_all_projective_targets.mpr hg,
      hs,hr,hq,h4⟩

theorem fullStatement_of_mainConclusions (c : ArExplicit.Candidate)
    (h : ArExplicit.MainConclusions ArExplicit.BaseField c.R c.M) : FullStatement.{v} := by
  let s : System :=
    { algebraCarrier := c.R
      ring := c.ring
      scalarAlgebra := c.algebra
      moduleCarrier := c.M
      additiveGroup := c.addCommGroup
      action := c.module
      scalarAction := c.baseModule
      actionTower := c.tower }
  refine ⟨ArExplicit.parameters_algebraicallyIndependent,s,conclusions_iff.mp h,?_⟩
  intro E _ _
  let := ArExplicit.scalarExtensionModule K E c.R c.M
  refine ⟨ArExplicit.scalarExtensionModule K E c.R c.M,
    ArExplicit.scalarExtensionIsScalarTower K E c.R c.M,?_,?_⟩
  · intro a b r z
    exact ArExplicit.scalarExtension_smul_tmul K E c.R c.M a b r z
  · exact conclusions_iff.mp (h.scalarExtension E)

end ArExplicit.Statement

end

end OAI
