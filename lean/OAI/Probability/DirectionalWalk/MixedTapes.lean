import OAI.Probability.DirectionalWalk.LateEndpoints

namespace OAI

open MeasureTheory ProbabilityTheory Filter Preorder
open scoped ENNReal BigOperators Topology

namespace DirectionalZeroOne

open scoped Classical

def combineTapes {α : Type*} (p : (ℕ → α) × (ℕ → α)) : TwoTape α :=
  fun i => if i.1 then p.2 i.2 else p.1 i.2

lemma measurable_combineTapes {α : Type*} [MeasurableSpace α] :
    Measurable (combineTapes (α := α)) := by
  apply Measurable.of_eval
  intro i
  cases i with | mk b n =>
    cases b <;> simp only [combineTapes,↓reduceIte,Bool.false_eq_true] <;> fun_prop

lemma combineTapes_law {α : Type*} [MeasurableSpace α]
    (ν : Bool → Measure α) [∀ b, IsProbabilityMeasure (ν b)] :
    ((Measure.infinitePi (fun _ : ℕ => ν false)).prod
      (Measure.infinitePi (fun _ : ℕ => ν true))).map combineTapes = twoTapeLaw ν := by
  have hpair := (twoExtract_independent ν).map_prod_eq_prod_map_map
    (Measurable.of_eval (fun i => measurable_pi_apply (false,i))).aemeasurable
    (Measurable.of_eval (fun i => measurable_pi_apply (true,i))).aemeasurable
  rw [twoExtract_law,twoExtract_law] at hpair
  rw [← hpair,Measure.map_map measurable_combineTapes
    ((Measurable.of_eval (fun i => measurable_pi_apply (false,i))).prodMk
      (Measurable.of_eval (fun i => measurable_pi_apply (true,i))))]
  have he : combineTapes ∘ (fun Z : TwoTape α => ((fun i => Z (false,i)),(fun i => Z (true,i)))) = id := by
    funext Z
    funext i
    cases i with | mk b n => cases b <;> rfl
  rw [he,Measure.map_id]

noncomputable def mixedTapes {d : ℕ} (e : Step d) (p : (ℕ → Word d) × Path d) : TwoTape (Word d) :=
  combineTapes (p.1,slabs (axisDirection (oppositeStep e)) p.2)

lemma measurable_mixedTapes {d : ℕ} (e : Step d) : Measurable (mixedTapes e) :=
  measurable_combineTapes.comp
    (measurable_fst.prodMk ((measurable_slabs (axisDirection (oppositeStep e))).comp measurable_snd))

lemma mixedTapes_law {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (hell : StrictEllipticity μ) (e : Step d)
    (hp : ∀ b, 0 < annealed μ 0 (nonBacktracking (axisDirection (placedAxis e b)))) :
    letI : ∀ b, IsProbabilityMeasure (slabLaw μ (axisDirection (placedAxis e b))) :=
      fun b => slabLaw_probability μ _ (hp b)
    ((Measure.infinitePi (fun _ : ℕ => slabLaw μ (axisDirection e))).prod
      (conditioned μ (axisDirection (oppositeStep e)))).map (mixedTapes e) =
      twoTapeLaw (fun b => slabLaw μ (axisDirection (placedAxis e b))) := by
  let : ∀ b, IsProbabilityMeasure (slabLaw μ (axisDirection (placedAxis e b))) :=
    fun b => slabLaw_probability μ _ (hp b)
  let := slabLaw_probability μ (axisDirection e) (hp false)
  let := conditioned_probability μ (axisDirection (oppositeStep e)) (hp true)
  have hpminus : 0 < annealed μ 0 (nonBacktracking (axisDirection (oppositeStep e))) := hp true
  change (((Measure.infinitePi (fun _ : ℕ => slabLaw μ (axisDirection e))).prod
      (conditioned μ (axisDirection (oppositeStep e)))).map
    (combineTapes ∘ (fun p => (p.1,slabs (axisDirection (oppositeStep e)) p.2)))) = _
  have hf : Measurable (fun p : (ℕ → Word d) × Path d =>
      (p.1,slabs (axisDirection (oppositeStep e)) p.2)) :=
    measurable_fst.prodMk ((measurable_slabs (axisDirection (oppositeStep e))).comp measurable_snd)
  rw [← Measure.map_map measurable_combineTapes hf]
  have hmap := Measure.map_prod_map
    (Measure.infinitePi (fun _ : ℕ => slabLaw μ (axisDirection e)))
    (conditioned μ (axisDirection (oppositeStep e))) measurable_id
    (measurable_slabs (axisDirection (oppositeStep e)))
  simp only [Measure.map_id',Prod.map_def,Function.id_def] at hmap
  rw [← hmap,slabs_map_eq_infinitePi μ hell _ (axisDirection_ne_zero (oppositeStep e)) hpminus]
  exact combineTapes_law (fun b => slabLaw μ (axisDirection (placedAxis e b)))

lemma measurableSet_contactDepth {d : ℕ} (e : Step d) (h : ℕ) :
    MeasurableSet {Z : TwoTape (Word d) | contactDepth e Z h} := by
  have hsite (b : Bool) (i t : ℕ) : Measurable (fun Z : TwoTape (Word d) => opposedSite e Z b i t) := by
    unfold opposedSite opposedAnchor
    cases b <;> simp only [Bool.false_eq_true,↓reduceIte]
    · exact (Finset.measurable_sum _ (fun j _ => (measurable_of_countable wordEnd).comp
        (measurable_pi_apply (X := fun _ : Bool × ℕ => Word d) (false,j)))).neg.add ((measurable_of_countable (fun a : Word d => wordPath a t)).comp
          (measurable_pi_apply (X := fun _ : Bool × ℕ => Word d) (false,i)))
    · exact (measurable_const.add (Finset.measurable_sum _ (fun j _ =>
        (measurable_of_countable wordEnd).comp (measurable_pi_apply (X := fun _ : Bool × ℕ => Word d) (true,j))))).add
          ((measurable_of_countable (fun a : Word d => wordPath a t)).comp (measurable_pi_apply (X := fun _ : Bool × ℕ => Word d) (true,i)))
  have hdep (b : Bool) (y : Site d) : MeasurableSet {Z : TwoTape (Word d) | opposedDeparture e Z b y} := by
    simp only [opposedDeparture,Set.ofPred_exists]
    apply MeasurableSet.iUnion;intro i
    apply MeasurableSet.iUnion;intro t
    apply MeasurableSet.inter
    · exact (measurable_pi_apply (X := fun _ : Bool × ℕ => Word d) (b,i)) (Set.to_countable {a : Word d | t < a.1}).measurableSet
    · exact (hsite b i t) (measurableSet_singleton y)
  unfold contactDepth contactAt
  simp only [Set.ofPred_exists]
  exact MeasurableSet.iUnion (fun y => ((hdep false y).inter (hdep true y)).inter (MeasurableSet.const _))

end DirectionalZeroOne

end OAI
