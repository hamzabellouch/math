import OAI.Dynamics.EntropyCounterexample.MapData
import OAI.Dynamics.EntropyCounterexample.ClockLiftBridge
import OAI.Dynamics.EntropyCounterexample.SphereCharts

namespace OAI

noncomputable section

open scoped OnePoint

namespace Problem340.Construction

local instance : Fact ((0 : ℝ) < 100) := ⟨by norm_num⟩

lemma onePointClockGate_eq_ambient (z : Sphere) :
    SphereCutoffs.onePointClockGate z =
      SphereCutoffs.clockGateAmbient (complexSphereHomeomorph z).val := by
  induction z using OnePoint.rec with
  | infty =>
      symm
      apply SphereCutoffs.clockGateAmbient_eq_one
      norm_num [complexSphereHomeomorph_infty, chartNorthPole, chartNorthVector]
  | coe z =>
      change SphereCutoffs.affineClockGate z = SphereCutoffs.clockGate (sphereOfComplex z)
      symm
      apply SphereCutoffs.clockGate_eq_affineClockGate
      exact sphereOfComplex_val_two z

lemma concrete_clockIncrement_eq_ambient (L : ℝ) (hL : 2 < L)
    (t : AddCircle (100 : ℝ)) (z : Sphere) :
    clockIncrement (concreteData L hL) t z =
      Clock.ambientIncrement (ClockModel.clockHomeomorph t).val
        (SphereCutoffs.clockGateAmbient (complexSphereHomeomorph z).val) := by
  obtain ⟨r, hr, rfl⟩ := AddCircle.eq_coe_Ico t
  rw [clockIncrement, AddCircle.liftIco_zero_coe_apply hr,
    Clock.clockHomeomorph_val_real, Clock.ambientIncrement_parametrization]
  change Clock.increment r (SphereCutoffs.onePointClockGate z) = _
  rw [onePointClockGate_eq_ambient]

lemma concreteMap_clock_eq_update (L : ℝ) (hL : 2 < L) (x : RawManifold) :
    ClockModel.clockHomeomorph (concreteMap L hL x).1 =
      Clock.update (ClockModel.clockHomeomorph x.1)
        (SphereCutoffs.clockGateAmbient (complexSphereHomeomorph x.2.1).val) := by
  change ClockModel.clockHomeomorph
    (x.1 + (clockIncrement (concreteData L hL) x.1 x.2.1 : ℝ)) = _
  rw [concrete_clockIncrement_eq_ambient]
  exact (Clock.update_clockHomeomorph _ _).symm

def concreteClockAmbient (x : CounterexampleAmbient 3) : ClockAmbient :=
  Clock.ambientUpdate x.1 (SphereCutoffs.clockGateAmbient (x.2 0))

lemma contDiff_concreteClockAmbient {n : ℕ∞} :
    ContDiff ℝ n concreteClockAmbient := by
  apply Clock.contDiff_ambientUpdate contDiff_fst
  exact SphereCutoffs.contDiff_clockGateAmbient.comp
    ((contDiff_apply ℝ SphereAmbient (0 : Fin 4)).comp contDiff_snd)

lemma transported_concreteMap_clock_ambient (L : ℝ) (hL : 2 < L)
    (x : CounterexampleManifold 3) :
    ((ClockModel.productHomeomorph 3 complexSphereHomeomorph)
      (concreteMap L hL ((ClockModel.productHomeomorph 3 complexSphereHomeomorph).symm x))).1.val =
      concreteClockAmbient (standardEmbedding 3 x) := by
  let e := ClockModel.productHomeomorph 3 complexSphereHomeomorph
  obtain ⟨y, rfl⟩ := e.surjective x
  change (e (concreteMap L hL (e.symm (e y)))).1.val = _
  rw [e.symm_apply_apply]
  change (ClockModel.clockHomeomorph (concreteMap L hL y).1).val = _
  rw [concreteMap_clock_eq_update]
  rfl

end Problem340.Construction

end

end OAI
