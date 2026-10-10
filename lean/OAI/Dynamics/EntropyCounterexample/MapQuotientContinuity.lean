import OAI.Dynamics.EntropyCounterexample.Map
import OAI.Dynamics.EntropyCounterexample.ClockQuotient

namespace OAI

noncomputable section

open Set Filter
open scoped Topology OnePoint

namespace Problem340.Construction

lemma baseInput_clock_mem_of_ne_zero (D : SphereData) (i : Fin 3) (x : ℝ × Sphere)
    (hx : baseInput D i x.1 x.2 ≠ 0) : x.1 ∈ Ioo 8 12 := by
  have hα : preparationCoeff x.1 ≠ 0 := by
    intro h
    apply hx
    simp [baseInput, h]
  have hmem : x.1 ∈ Function.support preparationCoeff := hα
  rwa [preparationCoeff_support] at hmem

lemma continuous_input_of_baseInput (D : SphereData) (i : Fin 3)
    (hbase : Continuous (fun x : ℝ × Sphere => baseInput D i x.1 x.2)) :
    Continuous (fun x : AddCircle (100 : ℝ) × Sphere => input D i x.1 x.2) := by
  let : Fact ((0 : ℝ) < 100) := ⟨by norm_num⟩
  apply ClockQuotient.continuous_liftIco_of_strip_support hbase
  intro x hx
  have h := baseInput_clock_mem_of_ne_zero D i x hx
  constructor <;> linarith [h.1, h.2]

lemma continuous_clockIncrement (D : SphereData) (hg : Continuous D.gate) :
    Continuous (fun x : AddCircle (100 : ℝ) × Sphere => clockIncrement D x.1 x.2) := by
  let : Fact ((0 : ℝ) < 100) := ⟨by norm_num⟩
  unfold clockIncrement
  apply ClockQuotient.continuous_liftIco_of_periodic
    (f := fun x : ℝ × Sphere => Clock.increment x.1 (D.gate x.2))
    (fun z => Clock.increment_periodic (D.gate z))
  have hb : Continuous (fun x : ℝ × Sphere => Clock.barrier x.1) :=
    (Clock.contDiff_barrier (n := 1)).continuous.comp continuous_fst
  exact hb.add ((continuous_const.sub hb).mul (hg.comp continuous_snd))

lemma continuous_periodicReadout (i : Fin 3) : Continuous (periodicReadout i) := by
  let : Fact ((0 : ℝ) < 100) := ⟨by norm_num⟩
  apply AddCircle.liftIco_zero_continuous
  · have hz (t : ℝ) (ht : t ∉ Ioo 74 80) : readoutCoeff i t = 0 := by
      by_contra h
      have hm : t ∈ Function.support (readoutCoeff i) := h
      rw [readoutCoeff_support] at hm
      exact ht (readoutInterval_subset i hm)
    rw [hz 0 (by norm_num), hz 100 (by norm_num)]
  · exact (readoutCoeff_contDiff i (n := 1)).continuous.continuousOn

lemma continuous_periodicGain (D : SphereData) (ha : Continuous D.gain)
    (haper : Function.Periodic D.gain 100) : Continuous (periodicGain D) := by
  let : Fact ((0 : ℝ) < 100) := ⟨by norm_num⟩
  apply AddCircle.liftIco_zero_continuous
  · simpa using (haper 0).symm
  · exact ha.continuousOn

lemma continuous_readout (D : SphereData) (hS : Continuous D.saturation) :
    Continuous (fun x : AddCircle (100 : ℝ) × (Fin 3 → Sphere) => readout D x.1 x.2) := by
  apply continuous_const.mul
  apply continuous_finsetSum
  intro i _
  exact (Complex.continuous_ofReal.comp ((continuous_periodicReadout i).comp continuous_fst)).mul
    (hS.comp ((continuous_apply i).comp continuous_snd))

lemma continuous_rawMap_of_coefficients (D : SphereData)
    (hg : Continuous D.gate)
    (hinput : ∀ i : Fin 3,
      Continuous (fun x : AddCircle (100 : ℝ) × Sphere => input D i x.1 x.2))
    (hS : Continuous D.saturation) (hperiodicGain : Continuous (periodicGain D)) :
    Continuous (rawMap D) := by
  have hmain : Continuous (fun x : RawManifold => x.2.1) :=
    continuous_fst.comp continuous_snd
  have hregs : Continuous (fun x : RawManifold => x.2.2) :=
    continuous_snd.comp continuous_snd
  have hpair : Continuous (fun x : RawManifold => (x.1, x.2.1)) :=
    continuous_fst.prodMk hmain
  have hc := (continuous_clockIncrement D hg).comp hpair
  have hclock : Continuous (Prod.fst : RawManifold → AddCircle (100 : ℝ)) := continuous_fst
  have hpairRegs := hclock.prodMk hregs
  have hr := (continuous_readout D hS).comp hpairRegs
  have hgain := Complex.continuous_ofReal.comp
    (hperiodicGain.comp hclock)
  have hu (i : Fin 3) :=
    (hinput i).comp hpair
  exact (continuous_fst.add ((AddCircle.continuous_mk' 100).comp hc)).prodMk
    ((continuous_perturbedSquare.comp (hr.prodMk hmain)).prodMk
      (continuous_pi fun i => OnePoint.continuous_coe.comp
        ((hgain.mul (hS.comp ((continuous_apply i).comp hregs))).add (hu i))))

lemma continuous_rawMap_of_baseInputs (D : SphereData)
    (hg : Continuous D.gate)
    (hbase : ∀ i : Fin 3, Continuous (fun x : ℝ × Sphere => baseInput D i x.1 x.2))
    (hS : Continuous D.saturation) (ha : Continuous D.gain)
    (haper : Function.Periodic D.gain 100) : Continuous (rawMap D) :=
  continuous_rawMap_of_coefficients D hg
    (fun i => continuous_input_of_baseInput D i (hbase i)) hS
    (continuous_periodicGain D ha haper)

end Problem340.Construction

end

end OAI
