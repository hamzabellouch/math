import OAI.Probability.InvariantIsing.Pressure.RandomOrbitLaw

namespace OAI

/-! Transporting deterministic orbit bounds through the joint conditional law. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
namespace InvariantIsing

lemma ConditionalFieldOrbitLaw.ae_property {Ω : Type*} [MeasurableSpace Ω] {N : ℕ}
    (hN : 0 < N) (P : Measure Ω) (d : Ω → FieldSpectralData N) (Y : Ω → ℝ)
    (hd : Measurable d) (hY : Measurable Y)
    (H : Measure (Orthogonal N)) [SFinite H]
    (hlaw : ConditionalFieldOrbitLaw P d Y H)
    (Q : FieldSpectralData N × ℝ → Prop) (hQ : MeasurableSet {z | Q z})
    (hbound : ∀ data U, Q (data,dataPhysicalPressure data U)) :
    ∀ᵐ ω ∂P, Q (d ω,Y ω) := by
  apply ae_of_ae_map (hd.prodMk hY).aemeasurable
  rw [hlaw]
  apply (ae_map_iff (measurable_fst.prodMk (measurable_dataPhysicalPressure hN)).aemeasurable hQ).mpr
  exact Filter.Eventually.of_forall fun z => hbound z.1 z.2

end InvariantIsing

end

end OAI
