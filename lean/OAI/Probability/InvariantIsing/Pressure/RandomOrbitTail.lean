import OAI.Probability.InvariantIsing.Pressure.RandomOrbitIntegration
import OAI.Probability.InvariantIsing.Pressure.UniformPhysicalTail

namespace OAI

/-! A localized tail bound under the exact joint conditional orbit hypothesis. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace InvariantIsing

lemma conditional_orbit_tail_bound {Ω : Type*} [MeasurableSpace Ω] {N : ℕ}
    (hN : 0 < N) (P : Measure Ω) [IsProbabilityMeasure P]
    (d : Ω → FieldSpectralData N) (Y : Ω → ℝ) (hd : Measurable d) (hY : Measurable Y)
    (H : Measure (Orthogonal N)) [IsProbabilityMeasure H]
    (hlaw : ConditionalFieldOrbitLaw P d Y H) (K ε B : ℝ)
    (hbound : ∀ data : FieldSpectralData N, (∀ i, |data.1 i| ≤ K) →
      H.real {U | ε ≤ |dataPhysicalPressure data U-(∫ V, dataPhysicalPressure data V ∂H)|} ≤ B) :
    P {ω | (∀ i, |(d ω).1 i| ≤ K) ∧
      ε ≤ |Y ω-(∫ V, dataPhysicalPressure (d ω) V ∂H)|} ≤ ENNReal.ofReal B := by
  let mean := fun data : FieldSpectralData N => ∫ V, dataPhysicalPressure data V ∂H
  have hm : Measurable mean := measurable_dataPressureMean hN H
  let E : Set (FieldSpectralData N × ℝ) := {z | (∀ i, |z.1.1 i| ≤ K) ∧ ε ≤ |z.2-mean z.1|}
  have hK : MeasurableSet {z : FieldSpectralData N × ℝ | ∀ i, |z.1.1 i| ≤ K} := by
    simp only [ofPred_forall]
    apply MeasurableSet.iInter
    intro i
    exact measurableSet_le (((measurable_pi_apply i).comp
      (measurable_fst.comp measurable_fst)).abs) measurable_const
  have hE : MeasurableSet E := hK.inter
    (measurableSet_le measurable_const (measurable_snd.sub (hm.comp measurable_fst)).abs)
  have hp : Measurable (fun z : FieldSpectralData N × Orthogonal N =>
      (z.1,dataPhysicalPressure z.1 z.2)) :=
    measurable_fst.prodMk (measurable_dataPhysicalPressure hN)
  have he := congrArg (fun Q : Measure (FieldSpectralData N × ℝ) => Q E) hlaw
  rw [Measure.map_apply (hd.prodMk hY) hE,Measure.map_apply hp hE,
    Measure.prod_apply (hp hE)] at he
  let : IsProbabilityMeasure (P.map d) :=
    (Measure.isProbabilityMeasure_map_iff hd.aemeasurable).mpr inferInstance
  change P ((fun ω => (d ω,Y ω)) ⁻¹' E) ≤ _
  rw [he]
  calc
    _ ≤ ∫⁻ _data : FieldSpectralData N, ENNReal.ofReal B ∂P.map d := by
      apply lintegral_mono
      intro data
      dsimp only
      by_cases hdata : ∀ i, |data.1 i| ≤ K
      · have hevent : Prod.mk data ⁻¹' ((fun z : FieldSpectralData N × Orthogonal N =>
            (z.1,dataPhysicalPressure z.1 z.2)) ⁻¹' E)=
            {U | ε ≤ |dataPhysicalPressure data U-mean data|} := by
          ext U
          change ((∀ i, |data.1 i| ≤ K) ∧ ε ≤ |dataPhysicalPressure data U-mean data|) ↔ _
          exact and_iff_right hdata
        rw [hevent]
        have hb := ENNReal.ofReal_le_ofReal (hbound data hdata)
        rwa [measureReal_def,ENNReal.ofReal_toReal (measure_ne_top H _)] at hb
      · have hevent : Prod.mk data ⁻¹' ((fun z : FieldSpectralData N × Orthogonal N =>
            (z.1,dataPhysicalPressure z.1 z.2)) ⁻¹' E)=∅ := by
          ext U
          change ((∀ i, |data.1 i| ≤ K) ∧ ε ≤ |dataPhysicalPressure data U-mean data|) ↔ False
          simp only [hdata,false_and]
        rw [hevent,measure_empty]
        exact bot_le
    _ = _ := by simp

end InvariantIsing

end

end OAI
