import Mathlib
import OAI.Combinatorics.UniformKServer.CausalLevel
import OAI.Combinatorics.UniformKServer.LevelHeavyEdits
import OAI.Combinatorics.UniformKServer.LevelMassLedger

namespace OAI

noncomputable section

/-! The integrated auxiliary function is adapted to the old request history. -/
namespace UniformKServer.LevelMap.Data
open scoped Classical
variable {X : Type} [Fintype X] [MetricSpace X] {N H : ℕ}
local instance ixCA : DecidableEq (Fin N) := fun a b=>Classical.propDecidable (a=b)
local instance iyCA : DecidableEq (Fin H) := fun a b=>Classical.propDecidable (a=b)
local instance pairCA : DecidableEq (X × X) := fun a b=>Classical.propDecidable (a=b)

lemma heavyPotential_inputs (D : Data X N H) (c d : Fin N→X)
    (h v : Fin N→Prop) (q u : Fin H→Fin N→Prop) (t : ℕ)
    (hc : ∀ i : Fin N, i.val<t→c i=d i) (hh : ∀ i : Fin N, i.val<t→(h i↔v i)) (p : X) :
    (D.inputs c h q).heavyPotential t p=(D.inputs d v u).heavyPotential t p := by
  unfold heavyPotential
  congr 1
  apply HeavyProcess.centers_inputs
  · intro j hj
    simp only [heavyFlag,inputs]
    apply exists_congr
    intro hjN
    exact hh ⟨j,hjN⟩ hj
  · exact fun j hj=>point_inputs D c d h v q u t hc j hj

lemma auxiliary_inputs (D : Data X N H) (c d : Fin N→X)
    (h v : Fin N→Prop) (q u : Fin H→Fin N→Prop) (t : ℕ)
    (hc : ∀ i : Fin N, i.val<t→c i=d i) (hh : ∀ i : Fin N, i.val<t→(h i↔v i))
    (hq : ∀ a (i : Fin N), i.val<t→(q a i↔u a i)) (is : List (Fin H)) (p : X) :
    (D.inputs c h q).auxiliary is t p=(D.inputs d v u).auxiliary is t p := by
  have he (ω : Tape D) : (D.inputs c h q).keyPotential is t p ω=
      (D.inputs d v u).keyPotential is t p ω := by
    unfold keyPotential
    rw [heavyPotential_inputs D c d h v q u t hc hh p]
    congr 1
    unfold tierPotential
    congr 1
    apply List.map_congr_left
    intro i _
    unfold tierUncovered tierKey inputs
    rw [CausalRosters.labeled_inputs D.r (D.K i) (q i) (u i) c d t (hq i) hc]
  unfold auxiliary
  congr 1
  exact congrArg D.law.expect (funext he)

end UniformKServer.LevelMap.Data

end

end OAI
