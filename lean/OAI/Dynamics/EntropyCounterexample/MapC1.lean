import OAI.Dynamics.EntropyCounterexample.RealizedConstruction
import OAI.Dynamics.EntropyCounterexample.MapClockComponent
import OAI.Dynamics.EntropyCounterexample.C1CoordinatePullback

namespace OAI

noncomputable section

namespace Problem340.Construction

theorem realizedMap_clock_hasLocalC1Extension (L : ℝ) (hL : 2 < L) :
    HasLocalC1Extension (standardEmbedding 3)
      (fun x => (realizedMap L hL x).1.1) := by
  apply HasLocalC1Extension.of_contDiffOn isOpen_univ (fun _ => Set.mem_univ _)
    concreteClockAmbient contDiff_concreteClockAmbient.contDiffOn
  exact transported_concreteMap_clock_ambient L hL

theorem realizedMap_main_hasLocalC1Extension_of_model (L : ℝ) (hL : 2 < L)
    (hmain : HasLocalC1Extension modelEmbedding
      (fun x => (complexSphereHomeomorph (concreteMap L hL x).2.1).1)) :
    HasLocalC1Extension (standardEmbedding 3)
      (fun x => ((realizedMap L hL x).2 0).1) := by
  have h := hmain.precomp_ambient (eY := standardEmbedding 3) modelHomeomorph.symm
    (id : CounterexampleAmbient 3 → CounterexampleAmbient 3) contDiff_id
    (fun x => by simp [modelEmbedding])
  exact h

theorem isC1SelfMap_realizedMap_of_sphere_components (L : ℝ) (hL : 2 < L)
    (hmain : HasLocalC1Extension (standardEmbedding 3)
      (fun x => ((realizedMap L hL x).2 0).1))
    (hregister : ∀ i : Fin 3, HasLocalC1Extension (standardEmbedding 3)
      (fun x => ((realizedMap L hL x).2 i.succ).1)) :
    IsC1SelfMap 3 (realizedMap L hL) := by
  apply isC1SelfMap_of_coordinate_extensions
    (realizedMap_clock_hasLocalC1Extension L hL)
  intro i
  exact Fin.cases hmain hregister i

end Problem340.Construction

end

end OAI
