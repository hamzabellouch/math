import OAI.Analysis.SeparableQuotients.ChangedPredual

namespace OAI

noncomputable section

namespace SeparableQuotient
open Set TopologicalSpace
open scoped Classical
universe u

/-- CH refutes the real separable quotient assertion in every universe. -/
theorem negative_real (hCH : CH) : ¬ SQ.{u} ℝ := by
  intro hSQ
  let X := ActualSpace.X hCH
  let : NormedAddCommGroup X := inferInstance
  let : NormedSpace ℝ X := inferInstance
  let : CompleteSpace X := ActualSpace.X_complete hCH
  let XU := ULift.{u} X
  let : NormedAddCommGroup XU := inferInstance
  let : NormedSpace ℝ XU := inferInstance
  let : CompleteSpace XU := inferInstance
  let d : XU ≃L[ℝ] X := ContinuousLinearEquiv.ulift
  have hI : ¬ FiniteDimensional ℝ XU := by
    intro hh
    let := hh
    exact ActualSpace.X_infinite hCH
      (FiniteDimensional.of_injective d.symm.toLinearMap d.symm.injective)
  have hsq := hSQ XU hI
  let R : ActualSpace.E ≃L[ℝ] StrongDual ℝ XU :=
    (ActualSpace.twistedIso hCH).trans (d.symm.arrowCongr (ContinuousLinearEquiv.refl ℝ ℝ))
  let J : XU →L[ℝ] StrongDual ℝ ActualSpace.E :=
    (ActualSpace.X hCH).subtypeL.comp d.toContinuousLinearMap
  have hR (e : ActualSpace.E) (x : XU) : R e x = J x e := by
    exact ActualSpace.twistedIso_apply hCH e (d x)
  obtain ⟨F,hF,hFi,hFs,hsep⟩ := separable_restriction_of_quotient R J hR hsq
  let := hFs.separableSpace
  apply ActualSpace.X_restriction_nonseparable hCH F hF hFi
  apply hsep.mono
  rintro _ ⟨x,hx,rfl⟩
  refine ⟨d.symm ⟨x,hx⟩,?_⟩
  change (J (d.symm ⟨x,hx⟩)).comp F.subtypeL = (ActualSpace.restrict F) x
  simp only [J,ContinuousLinearMap.comp_apply,ContinuousLinearEquiv.coe_coe,d.apply_symm_apply]
  rfl

end SeparableQuotient

end

end OAI
