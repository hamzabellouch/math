import OAI.Geometry.RCD.Metric.FiniteMeasureCut
import OAI.Geometry.RCD.Metric.FiniteSeparationCode

namespace OAI

/-! # A measurable cut retains a fixed fraction of the off-diagonal mass

This is the specialization of Rajala--Sturm, arXiv:1207.6754v2, Lemma 3.1
needed for the branching argument. No normalization of the finite measure is
needed; the same constant works before or after restricting pairs.
-/

open Set Filter MeasureTheory
open scoped Topology
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MeasurableSpace X] [MeasurableSpace.CountablySeparated X]

theorem measurable_pair_separation (σ : Measure (X×X)) [IsFiniteMeasure σ]
    (hpos : 0<σ.real {z : X×X | z.1≠z.2}) :
    ∃ E : Set X, MeasurableSet E ∧
      σ.real {z : X×X | z.1≠z.2}/5<σ.real (E ×ˢ Eᶜ) := by
  classical
  obtain ⟨n,f,hf,hlarge⟩ := exists_finite_separation_code σ
    (c:=4*σ.real {z : X×X | z.1≠z.2}/5) (by linarith)
  let τ := σ.map (fun z => (f z.1,f z.2))
  have hpair : Measurable (fun z : X×X => (f z.1,f z.2)) :=
    (hf.comp measurable_fst).prodMk (hf.comp measurable_snd)
  let : IsFiniteMeasure τ := inferInstance
  obtain ⟨b,hb⟩ := finite_measure_cut_ge_quarter τ
  let B : Set (Fin n → Bool) := {a | b a=true}
  let E := f ⁻¹' B
  have hB : MeasurableSet B := Set.toFinite B |>.measurableSet
  have hE : MeasurableSet E := hB.preimage hf
  have hsep : τ.real {z | z.1≠z.2}=σ.real {z : X×X | f z.1≠f z.2} := by
    exact congrArg ENNReal.toReal (Measure.map_apply hpair (Set.toFinite _ |>.measurableSet))
  have hcut : τ.real {z | b z.1=true ∧ b z.2=false}=σ.real (E ×ˢ Eᶜ) := by
    rw [Measure.real,Measure.map_apply hpair (Set.toFinite _ |>.measurableSet)]
    apply congrArg (fun A : Set (X×X) => (σ A).toReal)
    ext z
    simp only [mem_preimage,mem_ofPred_eq,mem_prod,mem_compl_iff,E,B]
    cases b (f z.2) <;> simp
  refine ⟨E,hE,?_⟩
  rw [hsep,hcut] at hb
  linarith

end RegularPointCoordinates

end

end OAI
