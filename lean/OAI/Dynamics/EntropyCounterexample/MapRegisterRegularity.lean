import OAI.Dynamics.EntropyCounterexample.MapData
import OAI.Dynamics.EntropyCounterexample.GainLocalExtension
import OAI.Dynamics.EntropyCounterexample.StandardRegisterUpdate

namespace OAI

noncomputable section

namespace Problem340.Construction

def registerInputInStandardCoordinates (L : ℝ) (hL : 2 < L) (i : Fin 3)
    (x : CounterexampleManifold 3) : ℂ :=
  input (concreteData L hL) i (clockHomeomorph.symm x.1)
    (complexSphereHomeomorph.symm (x.2 0))

def registerOutputInStandardCoordinates (L : ℝ) (hL : 2 < L) (i : Fin 3)
    (x : CounterexampleManifold 3) : StandardSphere2 :=
  standardRegisterUpdate (3 * L) (by linarith) (standardGain L x.1)
    (registerInputInStandardCoordinates L hL i x) (x.2 i.succ)

theorem registerOutputInStandardCoordinates_eq_raw (L : ℝ) (hL : 2 < L)
    (i : Fin 3) (x : CounterexampleManifold 3) :
    registerOutputInStandardCoordinates L hL i x =
      complexSphereHomeomorph
        ((concreteMap L hL
          (clockHomeomorph.symm x.1, complexSphereHomeomorph.symm (x.2 0),
            fun j : Fin 3 => complexSphereHomeomorph.symm (x.2 j.succ))).2.2 i) := by
  rw [registerOutputInStandardCoordinates, standardRegisterUpdate_eq_transport]
  simp only [concreteMap, rawMap, registerInputInStandardCoordinates,
    periodicGain, concreteData, standardGain, Complex.real_smul]

theorem concreteSaturation_hasLocalC1Extension (L : ℝ) (hL : 2 < L) :
    HasLocalC1Extension (fun x : StandardSphere2 => x.1)
      (standardSphereSaturation (3 * L) (by linarith)) := by
  intro x
  obtain ⟨U, hU, hx, A, hA, hcomm⟩ :=
    standardSphereSaturation_local_ambient (3 * L) (by linarith) x
  exact ⟨U, hU, hx, A, hA.of_le (by norm_num), hcomm⟩

theorem registerOutputInStandardCoordinates_hasLocalC1Extension
    (L : ℝ) (hL : 2 < L) (i : Fin 3)
    (hinput : HasLocalC1Extension (standardEmbedding 3)
      (registerInputInStandardCoordinates L hL i)) :
    HasLocalC1Extension (standardEmbedding 3)
      (fun x => (registerOutputInStandardCoordinates L hL i x : SphereAmbient)) := by
  have hgain := standardGain_hasLocalC1Extension_manifold L 3
  have hsat := (concreteSaturation_hasLocalC1Extension L hL).sphere_coordinate i.succ
  have hmul := (hgain.prodMk hsat).comp_contDiff
    (show ContDiff ℝ 1 (fun p : ℝ × ℂ => p.1 • p.2) from
      contDiff_fst.smul contDiff_snd)
  have hadd := (hmul.prodMk hinput).comp_contDiff
    (show ContDiff ℝ 1 (fun p : ℂ × ℂ => p.1 + p.2) from
      contDiff_fst.add contDiff_snd)
  simpa only [Function.comp_def, registerOutputInStandardCoordinates,
    standardRegisterUpdate] using hadd.comp_contDiff contDiff_sphereOfComplex_val

theorem concreteMap_register_hasLocalC1Extension
    (L : ℝ) (hL : 2 < L) (i : Fin 3)
    (hinput : HasLocalC1Extension (standardEmbedding 3)
      (registerInputInStandardCoordinates L hL i)) :
    HasLocalC1Extension (standardEmbedding 3)
      (fun x => (complexSphereHomeomorph
        ((concreteMap L hL
          (clockHomeomorph.symm x.1, complexSphereHomeomorph.symm (x.2 0),
            fun j : Fin 3 => complexSphereHomeomorph.symm (x.2 j.succ))).2.2 i) :
          SphereAmbient)) := by
  simpa only [← registerOutputInStandardCoordinates_eq_raw] using
    registerOutputInStandardCoordinates_hasLocalC1Extension L hL i hinput

end Problem340.Construction

end

end OAI
