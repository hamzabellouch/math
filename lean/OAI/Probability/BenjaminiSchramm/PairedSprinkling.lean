import OAI.Probability.CriticalPercolation.ProductMeasure.ProductEmbedding
import OAI.Probability.CriticalPercolation.ProductMeasure.ProductConditioning
import OAI.Probability.CriticalPercolation.ProductMeasure.MonotoneBernoulli
import OAI.Probability.UnimodularPercolation.Kernel.Sprinkling

namespace OAI

noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped Classical ENNReal

namespace CriticalPercolation.BernoulliProduct
variable {E : Type*}

def pairedParameters (q b : E → unitInterval) : E × Bool → unitInterval :=
  fun z => Percolation.pairParameter (q z.1) (b z.1) z.2

def whiteProjection (ω : Set (E × Bool)) : Set E :=
  (fun e => (e,true)) ⁻¹' ω

def blueProjection (ω : Set (E × Bool)) : Set E :=
  (fun e => (e,false)) ⁻¹' ω

def pairedUnion (ω : Set (E × Bool)) : Set E := {e | ∃ j, (e,j) ∈ ω}

lemma measurable_whiteProjection : Measurable (whiteProjection (E := E)) :=
  Measurable.of_eval fun e => measurable_set_mem (e,true)

lemma measurable_blueProjection : Measurable (blueProjection (E := E)) :=
  Measurable.of_eval fun e => measurable_set_mem (e,false)

lemma measurable_pairedUnion : Measurable (pairedUnion (E := E)) :=
  Measurable.of_eval fun e => (Measurable.of_discrete :
    Measurable (fun f : Bool → Prop => ∃ j, f j)).comp
      (Measurable.of_eval fun j => measurable_set_mem (e,j))

lemma pairedUnion_eq (ω : Set (E × Bool)) :
    pairedUnion ω=whiteProjection ω ∪ blueProjection ω := by
  ext e
  simp [pairedUnion,whiteProjection,blueProjection,Bool.exists_bool,or_comm]

lemma paired_white_law (q b : E → unitInterval) :
    (law (pairedParameters q b)).map whiteProjection=law q := by
  change (law (pairedParameters q b)).map (fun ω => (fun e => (e,true)) ⁻¹' ω)=law q
  simpa [whiteProjection,pairedParameters,Percolation.pairParameter,
    Function.comp_def] using law_map_preimage (pairedParameters q b)
      (fun e => (e,true)) (fun _ _ h => congrArg Prod.fst h)

lemma paired_blue_law (q b : E → unitInterval) :
    (law (pairedParameters q b)).map blueProjection=law b := by
  change (law (pairedParameters q b)).map (fun ω => (fun e => (e,false)) ⁻¹' ω)=law b
  simpa [blueProjection,pairedParameters,Percolation.pairParameter,
    Function.comp_def] using law_map_preimage (pairedParameters q b)
      (fun e => (e,false)) (fun _ _ h => congrArg Prod.fst h)

lemma paired_union_law (q b : E → unitInterval) :
    (law (pairedParameters q b)).map pairedUnion=
      law (fun e => Percolation.sprinkleParameter (q e) (b e)) := by
  simp only [law_eq_infinitePi]
  change (Measure.infinitePi (fun z : E × Bool => bitMeasure (pairedParameters q b z))).map
    (fun ω : E × Bool → Prop => fun e => ∃ j, ω (e,j))=
      Measure.infinitePi (fun e => bitMeasure (Percolation.sprinkleParameter (q e) (b e)))
  let c := MeasurableEquiv.curry E Bool Prop
  let f := fun g : E → Bool → Prop => fun e => ∃ j, g e j
  have hf : Measurable f := Measurable.of_eval fun e =>
    (Measurable.of_discrete : Measurable (fun g : Bool → Prop => ∃ j, g j)).comp
      (measurable_pi_apply e)
  change (Measure.infinitePi (fun z : E × Bool => bitMeasure (pairedParameters q b z))).map (f ∘ c)=_
  rw [←Measure.map_map hf c.measurable]
  rw [Measure.infinitePi_map_curry (fun e j => bitMeasure (pairedParameters q b (e,j)))]
  rw [Measure.infinitePi_map_pi _ (fun _ => Measurable.of_discrete)]
  congr 1
  funext e
  exact Percolation.map_bool_or (q e) (b e)

def whiteBlock (Q : Set E) : Set (E × Bool) := {z | z.1 ∈ Q ∧ z.2=true}

def erasedWhiteParameters (q : E → unitInterval) (Q : Set E) : E → unitInterval :=
  fun e => if e ∈ Q then 0 else q e

lemma pinned_white_parameters (q b : E → unitInterval) (Q : Set E) :
    pinnedParameters (pairedParameters q b) (whiteBlock Q) ∅=
      pairedParameters (erasedWhiteParameters q Q) b := by
  funext z
  rcases z with ⟨e,j⟩
  cases j <;> by_cases he : e ∈ Q <;>
    simp [pinnedParameters,pairedParameters,Percolation.pairParameter,
      whiteBlock,erasedWhiteParameters,he]

lemma fresh_paired_union_law (q b : E → unitInterval) (Q : Set E) :
    (law (pairedParameters q b)).map
      (pairedUnion ∘ forceOn (whiteBlock Q) ∅)=
      law (fun e => Percolation.sprinkleParameter (erasedWhiteParameters q Q e) (b e)) := by
  rw [←Measure.map_map measurable_pairedUnion (measurable_forceOn _ _),
    forceOn_map_law,pinned_white_parameters,paired_union_law]

def atParameters (q : E → unitInterval) (u : E → ℝ) : Set E := {e | u e < q e}

lemma measurable_atParameters (q : E → unitInterval) : Measurable (atParameters q) :=
  Measurable.of_eval fun e => (measurable_pi_apply e).lt measurable_const

lemma markLaw_map_atParameters (q : E → unitInterval) :
    (markLaw (E := E)).map (atParameters q)=law q := by
  rw [law_eq_infinitePi]
  exact (Measure.infinitePi_map_pi (fun _ : E => Priority.uniform01)
    (f := fun e t => t < (q e : ℝ))
    (fun _ => measurable_id.lt measurable_const)).trans
      (congrArg Measure.infinitePi (funext fun e => uniform01_map_threshold (q e)))

lemma law_mono_pointwise (q r : E → unitInterval) (hqr : ∀ e, q e ≤ r e)
    (A : Set (Set E)) (hA : MeasurableSet A) (hup : IsUpperSet A) :
    law q A ≤ law r A := by
  rw [←markLaw_map_atParameters q,←markLaw_map_atParameters r,
    Measure.map_apply (measurable_atParameters q) hA,
    Measure.map_apply (measurable_atParameters r) hA]
  apply measure_mono
  intro u hu
  apply hup _ hu
  intro e he
  exact (show u e < (q e : ℝ) from he).trans_le (hqr e)

end CriticalPercolation.BernoulliProduct

end

end OAI
