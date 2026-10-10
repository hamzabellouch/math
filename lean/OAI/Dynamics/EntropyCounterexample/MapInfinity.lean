import OAI.Dynamics.EntropyCounterexample.MapData
import OAI.Dynamics.EntropyCounterexample.RawInvariantInfinity

namespace OAI

noncomputable section

namespace Problem340.Construction

theorem rawMap_eq_rawUpdate (D : SphereData) :
    rawMap D = rawUpdate
      (fun x => clockIncrement D x.1 x.2.1)
      (fun x => readout D x.1 x.2.2)
      (fun x i => (periodicGain D x.1 : ℂ) * D.saturation (x.2.2 i) +
        input D i x.1 x.2.1) := rfl

theorem concreteMap_infinity_semiconj (L : ℝ) (hL : 2 < L) :
    Function.Semiconj (rawInfinityPoint 3) ClockAtInfinity.step (concreteMap L hL) := by
  intro t
  exact (concreteMap_infty_zero L hL t).symm

theorem concreteMap_mapsTo_infinitySet (L : ℝ) (hL : 2 < L) :
    Set.MapsTo (concreteMap L hL) (rawInfinitySet 3) (rawInfinitySet 3) := by
  rintro x ⟨t, rfl⟩
  exact ⟨ClockAtInfinity.step t, concreteMap_infinity_semiconj L hL t⟩

theorem concreteMap_periodic_on_infinitySet (L : ℝ) (hL : 2 < L)
    {x : RawManifold} (hx : x ∈ rawInfinitySet 3) :
    (concreteMap L hL)^[100] x = x := by
  obtain ⟨t, rfl⟩ := hx
  have h := (concreteMap_infinity_semiconj L hL).iterate_right 100 t
  simpa only [ClockAtInfinity.step_period, id_eq] using h.symm

theorem coverEntropy_concreteInfinity_image (L : ℝ) (hL : 2 < L)
    {X : Type*} [UniformSpace X] {T : X → X}
    {φ : RawManifold → X} (hφ : Continuous φ)
    (hsem : Function.Semiconj φ (concreteMap L hL) T) :
    Dynamics.coverEntropy T (φ '' rawInfinitySet 3) = 0 := by
  rw [rawInfinitySet, ← Set.range_comp]
  apply ClockAtInfinity.coverEntropy_clockImage
    (hφ.comp (continuous_rawInfinityPoint 3))
  intro t
  exact (congrArg φ (concreteMap_infinity_semiconj L hL t)).trans
    (hsem (rawInfinityPoint 3 t))

end Problem340.Construction

end

end OAI
