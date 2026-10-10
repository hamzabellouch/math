import OAI.Probability.ProjectionMoments.Stopping

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace
namespace NoiselessRegression
namespace Learner
universe u
variable {d M T : ℕ} {Ω : Type u} [MeasurableSpace Ω]

instance runStatusMeasurable : MeasurableSpace (RunStatus M) := ⊤
instance runStatusSingleton : MeasurableSingletonClass (RunStatus M) := ⟨fun _ => trivial⟩

lemma measurable_countable_select {X Y J : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [MeasurableSpace J] [MeasurableSingletonClass J] [Countable J]
    {f : J → X → Y} (hf : ∀ j, Measurable (f j)) {g : X → J} (hg : Measurable g) :
    Measurable (fun x => f (g x) x) :=
  (measurable_from_prod_countable_right (f := fun z : J × X => f z.1 z.2) hf).comp (hg.prodMk measurable_id)

lemma measurable_run (L : Learner d M T Ω) (hL : L.MeasurableRules) (n : ℕ) :
    Measurable (fun z : UnitSphere d × (Ω × Samples d T) => L.run z.1 z.2.1 z.2.2 n) := by
  classical
  induction n with
  | zero =>
    exact (measurable_of_finite (fun a : Bool × State M =>
      if a.1 then Sum.inr (0,a.2) else Sum.inl a.2)).comp
        (hL.initial.comp (measurable_fst.comp measurable_snd))
  | succ n ih =>
    let F : RunStatus M → (UnitSphere d × (Ω × Samples d T)) → RunStatus M := fun j z =>
      match j with
      | .inr done => .inr done
      | .inl j => if hn : n < T then
          let row := z.2.2 ⟨n,hn⟩
          let a := L.transition (n+1) z.2.1 j (row,⟪row,z.1.val⟫)
          if a.1 then .inr (n+1,a.2) else .inl a.2
        else .inl j
    change Measurable (fun z => F (L.run z.1 z.2.1 z.2.2 n) z)
    apply measurable_countable_select _ ih
    intro j
    cases j with
    | inr done => exact measurable_const
    | inl j =>
      dsimp [F]
      split_ifs with hn
      · exact (measurable_of_finite (fun a : Bool × State M =>
          if a.1 then Sum.inr (n+1,a.2) else Sum.inl a.2)).comp
            ((hL.transition (n+1) j).comp (show Measurable (fun z : UnitSphere d × (Ω × Samples d T) =>
              (z.2.1,(z.2.2 ⟨n,hn⟩,⟪z.2.2 ⟨n,hn⟩,z.1.val⟫))) from by fun_prop))
      · exact measurable_const

lemma measurable_terminal (L : Learner d M T Ω) (hL : L.MeasurableRules) :
    Measurable (fun z : UnitSphere d × (Ω × Samples d T) => L.terminal z.1 z.2.1 z.2.2) := by
  exact (measurable_of_countable (fun j : RunStatus M =>
    match j with | .inl j => (T,j) | .inr done => done)).comp (L.measurable_run hL T)

lemma measurable_estimate (L : Learner d M T Ω) (hL : L.MeasurableRules) :
    Measurable (fun z : UnitSphere d × (Ω × Samples d T) => L.estimate z.1 z.2.1 z.2.2) := by
  exact measurable_countable_select (f := fun a z => L.output a.1 z.2.1 a.2)
    (fun a => (hL.output a.1 a.2).comp (by fun_prop)) (L.measurable_terminal hL)

lemma admissible_of_measurable (L : Learner d M T Ω) (hL : L.MeasurableRules) (ρ : Measure Ω) :
    L.Admissible ρ := by
  refine ⟨hL.initial.aemeasurable,fun t j => (hL.transition t j).aemeasurable,
    fun t j => (hL.output t j).aemeasurable,?_,(L.measurable_estimate hL).aemeasurable⟩
  intro s
  exact ((L.measurable_estimate hL).comp (measurable_const.prodMk measurable_id)).aemeasurable

end Learner

universe u

lemma joint_sphere_sample_observation_quasi {d T : ℕ} (hd : 3 ≤ d)
    {Ω : Type u} [MeasurableSpace Ω] (ρ : Measure Ω) [SFinite ρ] (i : Fin T) :
    Measure.QuasiMeasurePreserving
      (fun z : UnitSphere d × (Ω × Samples d T) => (z.2.1,(z.2.2 i,⟪z.1.val,z.2.2 i⟫)))
      ((uniformSphere d).prod (ρ.prod (sampleLaw d T))) (ρ.prod (observationReference d)) := by
  let : NeZero d := ⟨by omega⟩
  have hp := (measurePreserving_prodAssoc ρ (uniformSphere d) (sampleLaw d T)).comp
    (((Measure.measurePreserving_swap (μ := uniformSphere d) (ν := ρ)).prod
      (MeasurePreserving.id (sampleLaw d T))).comp
        ((measurePreserving_prodAssoc (uniformSphere d) ρ (sampleLaw d T)).symm
          MeasurableEquiv.prodAssoc))
  have h := QuasiMeasurePreserving.prodMap (Measure.QuasiMeasurePreserving.id ρ)
    (sphere_sample_observation_quasi (E := Vector d) (by simpa using hd) i)
  exact h.comp hp.quasiMeasurePreserving

namespace Learner
variable {d M T : ℕ} {Ω : Type u} [MeasurableSpace Ω]

theorem exists_borel_version (L : Learner d M T Ω) (ρ : Measure Ω) [SFinite ρ]
    (hd : 3 ≤ d)
    (hi : AEMeasurable L.initialChoice ρ)
    (ht : ∀ t j, AEMeasurable (fun z : Ω × (Vector d × ℝ) => L.transition t z.1 j z.2)
      (ρ.prod (observationReference d)))
    (ho : ∀ t j, AEMeasurable (fun ω => L.output t ω j) ρ) :
    ∃ L' : Learner d M T Ω, L'.MeasurableRules ∧
      (∀ᵐ z ∂((uniformSphere d).prod (ρ.prod (sampleLaw d T))),
        (∀ n, L.run z.1 z.2.1 z.2.2 n = L'.run z.1 z.2.1 z.2.2 n) ∧
        L.estimate z.1 z.2.1 z.2.2 = L'.estimate z.1 z.2.1 z.2.2) := by
  classical
  let L' : Learner d M T Ω := ⟨hi.mk _,fun t ω j obs => (ht t j).mk _ (ω,obs),
    fun t ω j => (ho t j).mk _ ω⟩
  have hL' : L'.MeasurableRules := ⟨hi.measurable_mk,fun t j => (ht t j).measurable_mk,
    fun t j => (ho t j).measurable_mk⟩
  refine ⟨L',hL',?_⟩
  let μ := (uniformSphere d).prod (ρ.prod (sampleLaw d T))
  have hp : Measure.QuasiMeasurePreserving (fun z : UnitSphere d × (Ω × Samples d T) => z.2.1) μ ρ :=
    QuasiMeasurePreserving.fst Measure.quasiMeasurePreserving_snd
  have hinit : ∀ᵐ z ∂μ, L.initialChoice z.2.1 = L'.initialChoice z.2.1 := hp.ae hi.ae_eq_mk
  have hout : ∀ᵐ z ∂μ, ∀ t j, L.output t z.2.1 j = L'.output t z.2.1 j := by
    simp only [ae_all_iff]
    intro t j
    exact hp.ae (ho t j).ae_eq_mk
  have htrans : ∀ᵐ z ∂μ, ∀ t j (i : Fin T),
      L.transition t z.2.1 j (z.2.2 i,⟪z.2.2 i,z.1.val⟫) =
      L'.transition t z.2.1 j (z.2.2 i,⟪z.2.2 i,z.1.val⟫) := by
    simp only [ae_all_iff]
    intro t j i
    simpa only [real_inner_comm] using (joint_sphere_sample_observation_quasi hd ρ i).ae (ht t j).ae_eq_mk
  filter_upwards [hinit,hout,htrans] with z hi ho ht
  have hr (n : ℕ) : L.run z.1 z.2.1 z.2.2 n = L'.run z.1 z.2.1 z.2.2 n := by
    induction n with
    | zero => simp only [run,start,hi]
    | succ n ih =>
      rw [run,run,ih]
      cases L'.run z.1 z.2.1 z.2.2 n with
      | inr done => rfl
      | inl j =>
        split_ifs with hn
        · dsimp only
          rw [ht (n+1) j ⟨n,hn⟩]
        · rfl
  refine ⟨hr,?_⟩
  have he : L.terminal z.1 z.2.1 z.2.2 = L'.terminal z.1 z.2.1 z.2.2 := by
    simp only [terminal,hr]
  simp only [estimate,he,ho]

lemma aemeasurable_terminal_of_rules (L : Learner d M T Ω) (ρ : Measure Ω) [SFinite ρ]
    (hd : 3 ≤ d) (hL : L.Admissible ρ) :
    AEMeasurable (fun z : UnitSphere d × (Ω × Samples d T) => L.terminal z.1 z.2.1 z.2.2)
      ((uniformSphere d).prod (ρ.prod (sampleLaw d T))) := by
  obtain ⟨L',hL',he⟩ := L.exists_borel_version ρ hd hL.initialChoice hL.transition hL.output
  apply (L'.measurable_terminal hL').aemeasurable.congr
  filter_upwards [he] with z hz
  simp only [terminal,hz.1]

lemma uniformSuccess_borel_version (L : Learner d M T Ω) (ρ : Measure Ω) [SFinite ρ]
    (hd : 3 ≤ d) (hL : L.Admissible ρ) :
    ∃ L' : Learner d M T Ω, L'.MeasurableRules ∧ L'.Admissible ρ ∧
      ∀ ε, L.uniformSuccess ρ ε = L'.uniformSuccess ρ ε := by
  obtain ⟨L',hL',he⟩ := L.exists_borel_version ρ hd hL.initialChoice hL.transition hL.output
  refine ⟨L',hL',L'.admissible_of_measurable hL' ρ,fun ε => measure_congr ?_⟩
  filter_upwards [he] with z hz
  rw [hz.2]

end Learner
end NoiselessRegression

end

end OAI
