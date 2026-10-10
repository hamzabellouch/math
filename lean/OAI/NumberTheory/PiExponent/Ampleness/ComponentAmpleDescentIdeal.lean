import OAI.NumberTheory.PiExponent.LocalAlgebra.IdealPowerFiltration

namespace OAI

namespace PiExponentSeshadri.ComponentAmpleDescent
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open IdealModule
variable {X : Scheme.{0}}

theorem ideal_le_annihilator_closedModule {I J : X.IdealSheafData}
    (h : I * J = ⊥) (U : X.affineOpens) :
    J.ideal U ≤ Module.annihilator Γ(X,U.1) Γ(closedModule I,U.1) := by
  intro a ha
  apply Module.mem_annihilator.mpr
  intro m
  have hinj : Function.Injective ((closedInclusion I).val.app (op U.1)) := by
    let : Mono (closedInclusion I).val :=
      inferInstanceAs (Mono ((Scheme.Modules.toPresheafOfModules X).map (closedInclusion I)))
    exact PresheafOfModules.injective_of_mono (closedInclusion I).val (op U.1)
  apply hinj
  have hm : (closedInclusion I).app U.1 m ∈ I.ideal U := by
    rw [← closed_image I U]
    exact ⟨m,rfl⟩
  have hp := Ideal.mul_mem_mul_rev (R := Γ(X,U.1)) hm ha
  let b : Γ(X,U.1) := (closedInclusion I).app U.1 m
  have hz : a * b = 0 := by
    have hh : I.ideal U * J.ideal U = ⊥ := congrArg (fun K : X.IdealSheafData => K.ideal U) h
    simpa only [hh,Ideal.mem_bot] using hp
  exact (((closedInclusion I).app_smul (r := a) (x := m)).trans hz).trans
    ((closedInclusion I).app U.1).hom.map_zero.symm

theorem ideal_mul_eq_bot_of_reduced_cover [IsReduced X]
    {I J : X.IdealSheafData} (h : I.support ⊔ J.support = ⊤) : I * J = ⊥ := by
  apply Scheme.IdealSheafData.support_eq_top_iff.mp
  simpa only [Scheme.IdealSheafData.support_mul] using h

theorem ideal_le_annihilator_closedModule_of_reduced_cover [IsReduced X]
    {I J : X.IdealSheafData} (h : I.support ⊔ J.support = ⊤) (U : X.affineOpens) :
    J.ideal U ≤ Module.annihilator Γ(X,U.1) Γ(closedModule I,U.1) :=
  ideal_le_annihilator_closedModule (ideal_mul_eq_bot_of_reduced_cover h) U

end
end PiExponentSeshadri.ComponentAmpleDescent

end OAI
