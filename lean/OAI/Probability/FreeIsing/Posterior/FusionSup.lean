import Mathlib.MeasureTheory.Function.FactorsThrough
import OAI.Probability.FreeIsing.Conditioning.DiscreteConditioning
import OAI.Probability.FreeIsing.Spins.ObservationFusion

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace Problem367

local instance : MeasurableSingletonClass IsingSpin := ⟨fun _ => trivial⟩

theorem condExp_spin_comap_sup_eq_binaryFusion
    {Ω A B : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    [mA : MeasurableSpace A] [mB : MeasurableSpace B]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {S : Ω → IsingSpin} {X : Ω → A} {Y : Ω → B}
    (hS : Measurable S) (hX : Measurable X) (hY : Measurable Y)
    (hfair : ∀ a : IsingSpin, P {ω | S ω = a} = (1 / 2 : ENNReal))
    (hInd : X ⟂ᵢ[S, hS; P] Y)
    (hL : ∀ᵐ ω ∂P, |(P[fun ω => spinSign (S ω) | mA.comap X]) ω| < 1)
    (hR : ∀ᵐ ω ∂P, |(P[fun ω => spinSign (S ω) | mB.comap Y]) ω| < 1) :
    P[fun ω => spinSign (S ω) | mA.comap X ⊔ mB.comap Y] =ᵐ[P]
      fun ω => binaryFusion (P[fun ω => spinSign (S ω) | mA.comap X] ω)
        (P[fun ω => spinSign (S ω) | mB.comap Y] ω) := by
  obtain ⟨q, hq, hqe⟩ :=
    (show Measurable[mA.comap X]
      (P[fun ω => spinSign (S ω) | mA.comap X]) from
      stronglyMeasurable_condExp.measurable).exists_eq_measurable_comp
  obtain ⟨r, hr, hre⟩ :=
    (show Measurable[mB.comap Y]
      (P[fun ω => spinSign (S ω) | mB.comap Y]) from
      stronglyMeasurable_condExp.measurable).exists_eq_measurable_comp
  have hpostX : P[fun ω => spinSign (S ω) | mA.comap X] =ᵐ[P] fun ω => q (X ω) :=
    Filter.Eventually.of_forall (congrFun hqe)
  have hpostY : P[fun ω => spinSign (S ω) | mB.comap Y] =ᵐ[P] fun ω => r (Y ω) :=
    Filter.Eventually.of_forall (congrFun hre)
  have h := condExp_spin_given_observation_pair_eq_binaryFusion hS hX hY hq hr
    hpostX hpostY (by simpa only [hqe, Function.comp_apply] using hL)
    (by simpa only [hre, Function.comp_apply] using hR) hfair
    (fun a => indepFun_cond_fiber_of_condIndepFun hS hX hY hInd a)
  simpa only [Prod.instMeasurableSpace, MeasurableSpace.comap_prodMk,
    hqe, hre, Function.comp_apply] using h

end Problem367

end

end OAI
