import OAI.Geometry.RCD.Metric.MeasurablePairSeparation

namespace OAI

/-! # Restricting paired paths to two separated marginals

The retained mass is quantitative. Restriction preserves every previously
established almost-everywhere equality between the paired observables.
-/

open Set Filter MeasureTheory
noncomputable section
namespace RegularPointCoordinates
variable {Ω X Y : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
  [MeasurableSpace Y] [MeasurableSpace.CountablySeparated X] [MeasurableEq X]

theorem exists_separated_restriction (σ : Measure Ω) [IsFiniteMeasure σ]
    {f g : Ω → X} (hf : Measurable f) (hg : Measurable g)
    (hpos : 0<σ.real {z | f z≠g z}) :
    ∃ S : Set Ω, MeasurableSet S ∧
      σ.real {z | f z≠g z}/5<(σ.restrict S).real univ ∧
      (σ.restrict S).map f ⟂ₘ (σ.restrict S).map g := by
  let τ := σ.map (fun z => (f z,g z))
  have hfg : Measurable (fun z => (f z,g z)) := hf.prodMk hg
  have hdiff : MeasurableSet {z : X×X | z.1≠z.2} :=
    (measurableSet_eq_fun measurable_fst measurable_snd).compl
  have hmass : τ.real {z : X×X | z.1≠z.2}=σ.real {z | f z≠g z} :=
    congrArg ENNReal.toReal (Measure.map_apply hfg hdiff)
  obtain ⟨E,hE,hcut⟩ := measurable_pair_separation τ (by rw [hmass]; exact hpos)
  let S := (fun z => (f z,g z)) ⁻¹' (E ×ˢ Eᶜ)
  have hS : MeasurableSet S := (hE.prod hE.compl).preimage hfg
  refine ⟨S,hS,?_,?_⟩
  · rw [hmass] at hcut
    have hscut : τ.real (E ×ˢ Eᶜ)=(σ.restrict S).real univ := by
      rw [Measure.real,Measure.map_apply hfg (hE.prod hE.compl),Measure.real,
        Measure.restrict_apply_univ]
    rwa [hscut] at hcut
  · refine ⟨Eᶜ,hE.compl,?_,?_⟩
    · rw [Measure.map_apply hf hE.compl,Measure.restrict_apply (hE.compl.preimage hf)]
      have hz : f ⁻¹' Eᶜ ∩ S=∅ := by
        ext z
        simp [S]
        tauto
      rw [hz,measure_empty]
    · rw [compl_compl,Measure.map_apply hg hE,Measure.restrict_apply (hE.preimage hg)]
      have hz : g ⁻¹' E ∩ S=∅ := by
        ext z
        simp [S]
        tauto
      rw [hz,measure_empty]

omit [MeasurableSpace.CountablySeparated X] [MeasurableEq X] in
theorem restricted_observables_equal (σ : Measure Ω) {S : Set Ω}
    {f g : Ω → Y} (heq : f=ᵐ[σ] g) :
    (σ.restrict S).map f=(σ.restrict S).map g :=
  Measure.map_congr (heq.filter_mono (Measure.restrict_le_self.absolutelyContinuous.ae_le))

end RegularPointCoordinates

end

end OAI
