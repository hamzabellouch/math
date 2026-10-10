import OAI.Dynamics.EntropyCounterexample.MapRegisterRegularity
import OAI.Dynamics.EntropyCounterexample.RealizedConstruction

namespace OAI

noncomputable section

namespace Problem340.Construction

theorem analyticClockHomeomorph_eq_model :
    Problem340.clockHomeomorph = ClockModel.clockHomeomorph := rfl

theorem registerInputInStandardCoordinates_modelHomeomorph
    (L : ℝ) (hL : 2 < L) (i : Fin 3) (x : RawManifold) :
    registerInputInStandardCoordinates L hL i (modelHomeomorph x) =
      input (concreteData L hL) i x.1 x.2.1 := by
  simp only [registerInputInStandardCoordinates, modelHomeomorph_clock,
    modelHomeomorph_main, analyticClockHomeomorph_eq_model,
    Homeomorph.symm_apply_apply]

theorem realizedMap_register_eq_standardOutput
    (L : ℝ) (hL : 2 < L) (i : Fin 3) (x : CounterexampleManifold 3) :
    (realizedMap L hL x).2 i.succ = registerOutputInStandardCoordinates L hL i x := by
  rw [registerOutputInStandardCoordinates_eq_raw]
  rfl

theorem realizedMap_register_hasLocalC1Extension
    (L : ℝ) (hL : 2 < L) (i : Fin 3)
    (hinput : HasLocalC1Extension (standardEmbedding 3)
      (registerInputInStandardCoordinates L hL i)) :
    HasLocalC1Extension (standardEmbedding 3)
      (fun x => ((realizedMap L hL x).2 i.succ).1) := by
  simpa only [realizedMap_register_eq_standardOutput] using
    registerOutputInStandardCoordinates_hasLocalC1Extension L hL i hinput

end Problem340.Construction

end

end OAI
