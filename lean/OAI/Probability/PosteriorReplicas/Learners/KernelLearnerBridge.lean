import OAI.Probability.PosteriorReplicas.Learners.LearnerModelBridge

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter Function
open scoped ENNReal NNReal RealInnerProductSpace unitInterval
noncomputable section
namespace PosteriorRegression

lemma aemeasurable_completed_prod {X Y Z : Type*} [mX : MeasurableSpace X] [mY : MeasurableSpace Y]
    [MeasurableSpace Z] [MeasurableSpace.CountablyGenerated Z]
    (μ : Measure X) (ν : Measure Y) [SFinite ν]
    {f : X × Y → Z}
    (hf : @Measurable (NullMeasurableSpace X μ × Y) Z _ _ f) :
    AEMeasurable f (μ.prod ν) := by
  apply NullMeasurable.aemeasurable
  have hp : @Measurable (NullMeasurableSpace (X × Y) (μ.prod ν))
      (NullMeasurableSpace X μ × Y) _ _ (fun z => (z.1,z.2)) := by
    apply Measurable.prodMk
    · intro s hs
      have hs' : @NullMeasurableSet X mX s μ := hs
      change @NullMeasurableSet (X × Y) _ (Prod.fst ⁻¹' s) (μ.prod ν)
      exact @NullMeasurableSet.preimage (X × Y) X _ mX _ μ Prod.fst s hs'
        (Measure.quasiMeasurePreserving_fst (μ := μ) (ν := ν))
    · exact measurable_snd.nullMeasurable.measurable'
  exact hf.comp hp

lemma aemeasurable_countable_choice {X J Y : Type*} [MeasurableSpace X] [MeasurableSpace J]
    [MeasurableSpace Y] [Countable J] [MeasurableSingletonClass J]
    {μ : Measure X} {j : X → J} (hj : AEMeasurable j μ)
    {f : J → X → Y} (hf : ∀ a, AEMeasurable (f a) μ) :
    AEMeasurable (fun x => f (j x) x) μ := by
  let g : J → X → Y := fun a => (hf a).mk (f a)
  have hg : Measurable (fun z : X × J => g z.2 z.1) :=
    measurable_from_prod_countable_left (fun a => (hf a).measurable_mk)
  apply (hg.comp_aemeasurable (aemeasurable_id.prodMk hj)).congr
  filter_upwards [ae_all_iff.mpr (fun a => (hf a).ae_eq_mk)] with x hx
  exact (hx (j x)).symm

namespace Learner

instance runStatus_measurableSingleton (M : ℕ) : MeasurableSingletonClass (RunStatus M) where
  measurableSet_singleton r := by
    rcases r with a | done
    · simpa only [Set.image_singleton] using (measurableSet_inl_image (β := ℕ × State M) (s := {a})).mpr (measurableSet_singleton a)
    · simpa only [Set.image_singleton] using (measurableSet_inr_image (α := State M) (s := {done})).mpr (measurableSet_singleton done)

lemma uniform_experiment_of_steps {d M T : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (L : Learner d M T Ω) (ρ : Measure Ω) [IsProbabilityMeasure ρ]
    (hinit : Measurable L.initialChoice)
    (htrans : ∀ t a (i : Fin T), AEMeasurable
      (fun z : UnitSphere d × (Ω × Samples d T) =>
        L.transition t z.2.1 a (z.2.2 i,⟪z.2.2 i,z.1.val⟫))
      ((uniformSphere d).prod (ρ.prod (sampleLaw d T))))
    (hout : ∀ t a, Measurable (fun ω => L.output t ω a)) :
    AEMeasurable
      (fun z : UnitSphere d × (Ω × Samples d T) => L.estimate z.1 z.2.1 z.2.2)
      ((uniformSphere d).prod (ρ.prod (sampleLaw d T))) := by
  let μ := (uniformSphere d).prod (ρ.prod (sampleLaw d T))
  have hstart : Measurable L.start := by
    have he : L.start = (fun a : Bool × State M => if a.1 then Sum.inr (0,a.2) else Sum.inl a.2) ∘ L.initialChoice := rfl
    rw [he]
    exact (measurable_of_finite _).comp hinit
  have hr (n : ℕ) : AEMeasurable
      (fun z : UnitSphere d × (Ω × Samples d T) => L.run z.1 z.2.1 z.2.2 n) μ := by
    induction n with
    | zero => exact (hstart.comp measurable_snd.fst).aemeasurable
    | succ n ih =>
      have hf (r : RunStatus M) : AEMeasurable
          (fun z : UnitSphere d × (Ω × Samples d T) =>
            (match r with
            | .inr done => .inr done
            | .inl a => if hn : n<T then
                let v := L.transition (n+1) z.2.1 a (z.2.2 ⟨n,hn⟩,⟪z.2.2 ⟨n,hn⟩,z.1.val⟫)
                if v.1 then .inr (n+1,v.2) else .inl v.2
              else .inl a : RunStatus M)) μ := by
        rcases r with a | done
        · by_cases hn : n<T
          · simp only [dite_eq_left hn]
            exact (measurable_of_finite (fun v : Bool × State M =>
              if v.1 then Sum.inr (n+1,v.2) else Sum.inl v.2)).comp_aemeasurable (htrans (n+1) a ⟨n,hn⟩)
          · simpa only [dite_eq_right hn] using (aemeasurable_const : AEMeasurable (fun _ : UnitSphere d × (Ω × Samples d T) => Sum.inl a : _ → RunStatus M) μ)
        · exact aemeasurable_const
      exact aemeasurable_countable_choice ih hf
  have ht : AEMeasurable
      (fun z : UnitSphere d × (Ω × Samples d T) => L.terminal z.1 z.2.1 z.2.2) μ := by
    exact (measurable_of_countable (fun r : RunStatus M =>
      match r with | .inl a => (T,a) | .inr done => done)).comp_aemeasurable (hr T)
  have ho (r : ℕ × State M) : AEMeasurable
      (fun z : UnitSphere d × (Ω × Samples d T) => L.output r.1 z.2.1 r.2) μ :=
    ((hout r.1 r.2).comp measurable_snd.fst).aemeasurable
  exact aemeasurable_countable_choice ht ho

end Learner
end PosteriorRegression
end

end OAI
