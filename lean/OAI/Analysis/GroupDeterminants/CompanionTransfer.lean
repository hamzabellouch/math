import OAI.Analysis.GroupDeterminants.ProjectionCriterion

namespace OAI

noncomputable section
open scoped BigOperators Pointwise

namespace GroupRingDeterminant

theorem main_of_companion_input (input : CompanionInput) : MainStatement := by
  obtain ⟨K, hK, hKfinite, hKchar, H, hH, hHfg, a, b, hab, hba⟩ := input
  let := hK
  let := hKfinite
  let := hKchar
  let := hH
  let := hHfg
  obtain ⟨d, hd, X, Y, hXY, hYX⟩ := binary_matrix_of_finite_field K H a b hab hba
  let : Nonempty (Fin d) := ⟨⟨0, by omega⟩⟩
  obtain ⟨D, hD, P, hP, hPs, ht, Z, hZ, u, v, huv⟩ := lamp_projection_data X Y hXY hYX
  exact projection_criterion D hD P ⟨hP, hPs⟩ ht Z hZ u v huv

end GroupRingDeterminant

end

end OAI
