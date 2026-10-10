import OAI.Geometry.CylinderCovering.Radial.InducedFieldDefinitions
import OAI.Geometry.CylinderCovering.Radial.Nilpotent

namespace OAI

namespace CylinderCovering.RadialInducedField

theorem radial_induced_field : Statement := by
  intro F _ _ _ a b α β w lam hdim hab hw hder
  obtain ⟨e, he, hray, hsmooth, hzero⟩ :=
    RadialNilpotent.radial_induced_field hdim hab hw hder
  refine ⟨e, he, hray, hsmooth, ?_⟩
  intro z hz hangle
  have hang := (RadialNilpotent.angle_hasFDerivAt (e.symm z) (ne_of_gt hz)).comp z
    e.symm.hasFDerivAt
  simp only [Function.comp_def] at hang
  have hdw : HasFDerivAt (fun x : F => w ((e.symm x).2 / (e.symm x).1))
      ((fderiv ℝ (fun x : F => (e.symm x).2 / (e.symm x).1) z).smulRight
        (lam ((e.symm z).2 / (e.symm z).1) •
          (a + ((e.symm z).2 / (e.symm z).1) • b))) z := by
    convert! (hder _ hangle).hasFDerivAt.comp z hang.differentiableAt.hasFDerivAt using 1
  refine ⟨hdw.fderiv, ?_, hzero z hz hangle⟩
  rw [hang.fderiv]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe]
  have hinv : e.symm (a + ((e.symm z).2 / (e.symm z).1) • b) =
      (1, (e.symm z).2 / (e.symm z).1) := by
    apply e.injective
    simp only [e.apply_symm_apply, he, one_smul]
  rw [hinv]
  exact RadialNilpotent.angle_derivative_radial _ (ne_of_gt hz)

end CylinderCovering.RadialInducedField

end OAI
