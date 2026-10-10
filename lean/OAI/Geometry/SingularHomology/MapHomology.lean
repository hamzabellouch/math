import OAI.Dynamics.EntropyCounterexample.MapData
import OAI.Dynamics.EntropyCounterexample.MapContinuity
import OAI.Dynamics.EntropyCounterexample.MapQuotientContinuity
import OAI.Geometry.SingularHomology.SkewProductHomology

namespace OAI

noncomputable section

namespace Problem340.Construction

def rawClockFunction (D : SphereData) (x : RawManifold) : ℝ :=
  clockIncrement D x.1 x.2.1

def rawPerturbation (D : SphereData) (x : RawManifold) : ℂ :=
  readout D x.1 x.2.2

def rawRegisterFunction (D : SphereData) (x : RawManifold) (i : Fin 3) : ℂ :=
  (periodicGain D x.1 : ℂ) * D.saturation (x.2.2 i) + input D i x.1 x.2.1

theorem rawMap_eq_rawUpdate_coefficients (D : SphereData) :
    rawMap D = rawUpdate (rawClockFunction D) (rawPerturbation D)
      (rawRegisterFunction D) := rfl

theorem continuous_rawMap_of_rawCoefficients (D : SphereData)
    (hh : Continuous (rawClockFunction D)) (hC : Continuous (rawPerturbation D))
    (hR : Continuous (rawRegisterFunction D)) : Continuous (rawMap D) :=
  continuous_rawUpdate hh hC hR

def rawMapHomotopy (D : SphereData)
    (hh : Continuous (rawClockFunction D)) (hC : Continuous (rawPerturbation D))
    (hR : Continuous (rawRegisterFunction D)) :
    ContinuousMap.Homotopy
      ⟨(@rawNormalForm 3), continuous_rawNormalForm⟩
      ⟨rawMap D, continuous_rawMap_of_rawCoefficients D hh hC hR⟩ :=
  rawUpdateHomotopy hh hC hR

theorem realHomologyMap_rawMap_eq_normalForm (n : ℕ) (D : SphereData)
    (hh : Continuous (rawClockFunction D)) (hC : Continuous (rawPerturbation D))
    (hR : Continuous (rawRegisterFunction D)) :
    realHomologyMap n (rawMap D) (continuous_rawMap_of_rawCoefficients D hh hC hR) =
      realHomologyMap n rawNormalForm continuous_rawNormalForm :=
  realHomologyMap_rawUpdate_eq_normalForm n 3 hh hC hR

theorem rawMap_eigenvector_of_sphere (n : ℕ) (D : SphereData)
    (hh : Continuous (rawClockFunction D)) (hC : Continuous (rawPerturbation D))
    (hR : Continuous (rawRegisterFunction D))
    (c : ℝ) (v : RealSingularHomology n Sphere) (hv : v ≠ 0)
    (heig : realHomologyMap n rawSphereSquare continuous_rawSphereSquare v = c • v) :
    ∃ w : RealSingularHomology n RawManifold, w ≠ 0 ∧
      realHomologyMap n (rawMap D) (continuous_rawMap_of_rawCoefficients D hh hC hR) w = c • w :=
  rawUpdate_eigenvector_of_sphere n 3 hh hC hR c v hv heig

theorem continuous_rawCoefficients (D : SphereData)
    (hh : Continuous (fun p : AddCircle (100 : ℝ) × Sphere => clockIncrement D p.1 p.2))
    (hβ : ∀ i, Continuous (periodicReadout i))
    (ha : Continuous (periodicGain D)) (hS : Continuous D.saturation)
    (hU : ∀ i, Continuous (fun p : AddCircle (100 : ℝ) × Sphere => input D i p.1 p.2)) :
    Continuous (rawClockFunction D) ∧ Continuous (rawPerturbation D) ∧
      Continuous (rawRegisterFunction D) := by
  let p : RawManifold → AddCircle (100 : ℝ) × Sphere := fun x => (x.1, x.2.1)
  have hp : Continuous p := continuous_fst.prodMk (continuous_fst.comp continuous_snd)
  let clock : RawManifold → AddCircle (100 : ℝ) := Prod.fst
  have ht : Continuous clock := continuous_fst
  let regs (i : Fin 3) : RawManifold → Sphere := fun x => x.2.2 i
  have hr (i : Fin 3) : Continuous (regs i) :=
    (continuous_apply i).comp (continuous_snd.comp continuous_snd)
  constructor
  · have H := hh.comp hp
    exact H
  constructor
  · unfold rawPerturbation readout
    apply continuous_const.mul
    apply continuous_finsetSum
    intro i _
    have H := (Complex.continuous_ofReal.comp ((hβ i).comp ht)).mul (hS.comp (hr i))
    exact H
  · unfold rawRegisterFunction
    apply continuous_pi
    intro i
    have H := ((Complex.continuous_ofReal.comp (ha.comp ht)).mul (hS.comp (hr i))).add
      ((hU i).comp hp)
    exact H

theorem continuous_concrete_rawCoefficients (L : ℝ) (hL : 2 < L) :
    Continuous (rawClockFunction (concreteData L hL)) ∧
      Continuous (rawPerturbation (concreteData L hL)) ∧
      Continuous (rawRegisterFunction (concreteData L hL)) := by
  let D := concreteData L hL
  have hg : Continuous D.gate := SphereCutoffs.continuous_onePointClockGate
  have hS : Continuous D.saturation := sphereSaturation_continuous (3 * L) _
  have hbase (i : Fin 3) : Continuous (fun x : ℝ × Sphere => baseInput D i x.1 x.2) :=
    continuous_baseInput_of_standard_cutoffs D rfl rfl (by change 1 < L; linarith) i
  have ha : Continuous (periodicGain D) := by
    let : Fact ((0 : ℝ) < 100) := ⟨by norm_num⟩
    apply AddCircle.liftIco_zero_continuous
    · change gainProfile L 0 = gainProfile L 100
      rw [gainProfile_zero_outside (by norm_num), gainProfile_zero_outside (by norm_num)]
    · exact (gainProfile_contDiff L).continuous.continuousOn
  exact continuous_rawCoefficients D (continuous_clockIncrement D hg)
    continuous_periodicReadout ha hS (fun i => continuous_input_of_baseInput D i (hbase i))

theorem concreteMap_continuous_for_homotopy (L : ℝ) (hL : 2 < L) :
    Continuous (concreteMap L hL) := by
  obtain ⟨hh, hC, hR⟩ := continuous_concrete_rawCoefficients L hL
  exact continuous_rawMap_of_rawCoefficients (concreteData L hL) hh hC hR

def concreteMapHomotopy (L : ℝ) (hL : 2 < L) :
    ContinuousMap.Homotopy
      ⟨(@rawNormalForm 3), continuous_rawNormalForm⟩
      ⟨concreteMap L hL, concreteMap_continuous_for_homotopy L hL⟩ := by
  obtain ⟨hh, hC, hR⟩ := continuous_concrete_rawCoefficients L hL
  exact rawMapHomotopy (concreteData L hL) hh hC hR

theorem realHomologyMap_concreteMap_eq_normalForm (n : ℕ) (L : ℝ) (hL : 2 < L) :
    realHomologyMap n (concreteMap L hL) (concreteMap_continuous_for_homotopy L hL) =
      realHomologyMap n rawNormalForm continuous_rawNormalForm :=
  (realHomologyMap_eq_of_homotopy n continuous_rawNormalForm
    (concreteMap_continuous_for_homotopy L hL) (concreteMapHomotopy L hL)).symm

theorem concreteMap_eigenvector_of_sphere (n : ℕ) (L : ℝ) (hL : 2 < L)
    (c : ℝ) (v : RealSingularHomology n Sphere) (hv : v ≠ 0)
    (heig : realHomologyMap n rawSphereSquare continuous_rawSphereSquare v = c • v) :
    ∃ w : RealSingularHomology n RawManifold, w ≠ 0 ∧
      realHomologyMap n (concreteMap L hL) (concreteMap_continuous_for_homotopy L hL) w = c • w := by
  obtain ⟨hh, hC, hR⟩ := continuous_concrete_rawCoefficients L hL
  exact rawMap_eigenvector_of_sphere n (concreteData L hL) hh hC hR c v hv heig

end Problem340.Construction

end

end OAI
