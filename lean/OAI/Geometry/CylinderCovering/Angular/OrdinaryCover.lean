import OAI.Geometry.CylinderCovering.Angular.OrdinaryCaps
import OAI.Geometry.CylinderCovering.Angular.GeneralTheorem

namespace OAI

noncomputable section

namespace CylinderCovering.AngularOrdinaryCaps

theorem chosenRadius_constant {choice : CapChoice} (hc : choice ≠ .radial)
    (ε η l r : ℝ) : ∃ R : ℝ, ∀ q : ℝ, chosenRadius choice ε η l r q = R := by
  cases choice with
  | midpoint => exact ⟨midpointRadius ε η l r, fun _ => rfl⟩
  | maximum => exact ⟨maximumRadius ε η l r, fun _ => rfl⟩
  | radial => exact (hc rfl).elim

theorem ordinary_covers : OrdinaryCoverStatement := by
  intro η hη0 hη1 M hM
  obtain ⟨δ, A, hδ, hA, hgeneral⟩ := AngularGeneral.general_cap η hη0 hη1 M hM
  refine ⟨δ, A, hδ, hA, ?_⟩
  intro ε hε hεδ N hN a ha0 haN ha hmesh choice
  have hadm := ordinaryData_admissible choice hN ha0 haN ha hη0.le hM hmesh
  have hcon := hgeneral ε hε hεδ (ordinaryData choice N a ε η) hadm
  refine ⟨hcon, ?_⟩
  intro hc j hj
  apply hcon.2.2.2.2.2.2 j hj
  obtain ⟨R, hR⟩ := chosenRadius_constant hc ε η (a j) (a (j + 1))
  exact ⟨R, fun q _ => hR q⟩

end CylinderCovering.AngularOrdinaryCaps

end

end OAI
