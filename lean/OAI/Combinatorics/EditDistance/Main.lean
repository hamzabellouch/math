import OAI.Combinatorics.EditDistance.AlphabetLower
import OAI.Combinatorics.EditDistance.AlphabetSupremum
import OAI.Combinatorics.EditDistance.WholeMaps

namespace OAI

/-!
# Two-sided exponential bounds for edit-distance distortion
-/

universe u

theorem edit_distance_main : EditDistortion.MainClaim.{u} := by
  obtain ⟨c,hc,dL,hL⟩ := EditLower.all_lower_clauses.{u}
  obtain ⟨dU,hU⟩ := Filter.eventually_atTop.mp EditUpper.eventual_upper.{u}
  refine ⟨c,32,hc,by norm_num,max dL dU,?_⟩
  intro d hd
  obtain ⟨hl,hw,hs⟩ := hL d ((le_max_left _ _).trans hd)
  obtain ⟨hu,hsu⟩ := hU d ((le_max_right _ _).trans hd)
  exact ⟨fun A inst hA => ⟨hl A hA,hu A hA⟩,hw,hs,hsu⟩

end OAI
