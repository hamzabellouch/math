import OAI.Probability.FreeIsing.Estimates.FairSpin

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped Classical

namespace Problem367.RandomIndexSampling

theorem card_image_eq_of_same_fibers {ι κ τ : Type*}
    (s : Finset ι) (r : ι → κ) (q : ι → τ)
    (h : ∀ i ∈ s, ∀ j ∈ s, r i = r j ↔ q i = q j) :
    (s.image r).card = (s.image q).card := by
  classical
  revert h
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    intro h
    have hs : (s.image r).card = (s.image q).card :=
      ih (fun i hi j hj => h i (Finset.mem_insert_of_mem hi)
        j (Finset.mem_insert_of_mem hj))
    have hm : r a ∈ s.image r ↔ q a ∈ s.image q := by
      constructor
      · intro hr
        obtain ⟨i, hi, hir⟩ := Finset.mem_image.mp hr
        exact Finset.mem_image.mpr ⟨i, hi,
          (h i (Finset.mem_insert_of_mem hi) a (Finset.mem_insert_self _ _)).mp hir⟩
      · intro hq
        obtain ⟨i, hi, hiq⟩ := Finset.mem_image.mp hq
        exact Finset.mem_image.mpr ⟨i, hi,
          (h i (Finset.mem_insert_of_mem hi) a (Finset.mem_insert_self _ _)).mpr hiq⟩
    simp only [Finset.image_insert]
    by_cases hr : r a ∈ s.image r
    · rw [Finset.card_insert_of_mem hr, Finset.card_insert_of_mem (hm.mp hr), hs]
    · rw [Finset.card_insert_of_notMem hr,
        Finset.card_insert_of_notMem (fun hq => hr (hm.mpr hq)), hs]

variable {E I J A : Type*}
variable [MeasurableSpace E] [MeasurableSpace J] [MeasurableSpace A]
variable [Countable J] [MeasurableSingletonClass J]

theorem measurable_select (r : E → I → J) (hr : ∀ i, Measurable (fun e => r e i)) :
    Measurable (fun p : E × (J → A) => fun i => p.2 (r p.1 i)) := by
  apply Measurable.of_eval
  intro i
  have heval : Measurable (fun p : J × (J → A) => p.2 p.1) :=
    measurable_from_prod_countable_right (fun j => measurable_pi_apply j)
  exact heval.comp ((hr i |>.comp measurable_fst).prodMk measurable_snd)

theorem measurePreserving_select
    (μ : Measure E) [SFinite μ] (ν : Measure A) [IsProbabilityMeasure ν]
    (r : E → I → J) (hr : ∀ i, Measurable (fun e => r e i))
    (hinj : ∀ᵐ e ∂μ, Function.Injective (r e)) :
    MeasurePreserving
      (fun p : E × (J → A) => (p.1, fun i => p.2 (r p.1 i)))
      (μ.prod (Measure.infinitePi (fun _ : J => ν)))
      (μ.prod (Measure.infinitePi (fun _ : I => ν))) := by
  refine (MeasurePreserving.id μ).skew_product
    (g := fun (e : E) (u : J → A) (i : I) => u (r e i))
    (measurable_select r hr) ?_
  filter_upwards [hinj] with e he
  exact Measure.map_infinitePi_infinitePi_of_inj he

theorem map_select
    (μ : Measure E) [SFinite μ] (ν : Measure A) [IsProbabilityMeasure ν]
    (r : E → I → J) (hr : ∀ i, Measurable (fun e => r e i))
    (hinj : ∀ᵐ e ∂μ, Function.Injective (r e)) :
    (μ.prod (Measure.infinitePi (fun _ : J => ν))).map
      (fun p : E × (J → A) => (p.1, fun i => p.2 (r p.1 i))) =
      μ.prod (Measure.infinitePi (fun _ : I => ν)) :=
  (measurePreserving_select μ ν r hr hinj).map_eq

def Consistent (s : Finset I) (r : I → J) (η : I → A) : Prop :=
  ∀ i ∈ s, ∀ j ∈ s, r i = r j → η i = η j

omit [MeasurableSpace J] [MeasurableSpace A] [Countable J] [MeasurableSingletonClass J] in

theorem consistent_iff_of_same_fibers {K : Type*}
    (s : Finset I) (r : I → J) (q : I → K) (η : I → A)
    (h : ∀ i ∈ s, ∀ j ∈ s, r i = r j ↔ q i = q j) :
    Consistent s r η ↔ Consistent s q η := by
  constructor
  · intro hc i hi j hj hij
    exact hc i hi j hj ((h i hi j hj).mpr hij)
  · intro hc i hi j hj hij
    exact hc i hi j hj ((h i hi j hj).mp hij)

omit [MeasurableSpace J] [Countable J] [MeasurableSingletonClass J] in

theorem finite_cylinder_of_consistent [Nonempty A] [MeasurableSingletonClass A]
    (ν : Measure A) [IsProbabilityMeasure ν] (p : ENNReal)
    (hmass : ∀ a, ν {a} = p)
    (s : Finset I) (r : I → J) (η : I → A) (hc : Consistent s r η) :
    (Measure.infinitePi (fun _ : J => ν))
      {u : J → A | ∀ i ∈ s, u (r i) = η i} = p ^ (s.image r).card := by
  classical
  let a : J → A := fun j =>
    if h : ∃ i ∈ s, r i = j then η h.choose else Classical.arbitrary A
  have ha (i : I) (hi : i ∈ s) : a (r i) = η i := by
    dsimp only [a]
    split_ifs with h
    · exact hc h.choose h.choose_spec.1 i hi h.choose_spec.2
    · exact (h ⟨i, hi, rfl⟩).elim
  have hset : {u : J → A | ∀ i ∈ s, u (r i) = η i} =
      Set.pi (s.image r : Set J) (fun j => {a j}) := by
    ext u
    constructor
    · intro hu j hj
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hj
      exact (hu i hi).trans (ha i hi).symm
    · intro hu i hi
      exact (hu (r i) (Finset.mem_image.mpr ⟨i, hi, rfl⟩)).trans (ha i hi)
  rw [hset, Measure.infinitePi_pi _ (fun _ _ => measurableSet_singleton _)]
  simp only [hmass, Finset.prod_const]

omit [MeasurableSpace J] [Countable J] [MeasurableSingletonClass J] in

theorem finite_cylinder_eq_zero_of_not_consistent
    (ν : Measure A) [IsProbabilityMeasure ν]
    (s : Finset I) (r : I → J) (η : I → A) (hc : ¬ Consistent s r η) :
    (Measure.infinitePi (fun _ : J => ν))
      {u : J → A | ∀ i ∈ s, u (r i) = η i} = 0 := by
  have hset : {u : J → A | ∀ i ∈ s, u (r i) = η i} = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro u hu
    apply hc
    intro i hi j hj hij
    rw [← hu i hi, ← hu j hj, hij]
  rw [hset, measure_empty]

omit [MeasurableSpace J] [Countable J] [MeasurableSingletonClass J] in

theorem finite_cylinder [Nonempty A] [MeasurableSingletonClass A]
    (ν : Measure A) [IsProbabilityMeasure ν] (p : ENNReal)
    (hmass : ∀ a, ν {a} = p)
    (s : Finset I) (r : I → J) (η : I → A) :
    (Measure.infinitePi (fun _ : J => ν))
      {u : J → A | ∀ i ∈ s, u (r i) = η i} =
      if Consistent s r η then p ^ (s.image r).card else 0 := by
  classical
  by_cases hc : Consistent s r η
  · rw [ite_eq_left hc]
    exact finite_cylinder_of_consistent ν p hmass s r η hc
  · rw [ite_eq_right hc]
    exact finite_cylinder_eq_zero_of_not_consistent ν s r η hc

omit [MeasurableSpace J] [Countable J] [MeasurableSingletonClass J] in

theorem finite_cylinder_congr [Nonempty A] [MeasurableSingletonClass A]
    {K : Type*} (ν : Measure A) [IsProbabilityMeasure ν] (p : ENNReal)
    (hmass : ∀ a, ν {a} = p)
    (s : Finset I) (r : I → J) (q : I → K) (η : I → A)
    (h : ∀ i ∈ s, ∀ j ∈ s, r i = r j ↔ q i = q j) :
    (Measure.infinitePi (fun _ : J => ν))
      {u : J → A | ∀ i ∈ s, u (r i) = η i} =
    (Measure.infinitePi (fun _ : K => ν))
      {u : K → A | ∀ i ∈ s, u (q i) = η i} := by
  rw [finite_cylinder ν p hmass s r η, finite_cylinder ν p hmass s q η,
    consistent_iff_of_same_fibers s r q η h, card_image_eq_of_same_fibers s r q h]

theorem random_finite_cylinder [Nonempty A] [MeasurableSingletonClass A]
    (μ : Measure E) (ν : Measure A) [IsProbabilityMeasure ν] (p : ENNReal)
    (hmass : ∀ a, ν {a} = p)
    (s : Finset I) (r : E → I → J) (hr : ∀ i, Measurable (fun e => r e i))
    (η : I → A) :
    (μ.prod (Measure.infinitePi (fun _ : J => ν)))
      {z : E × (J → A) | ∀ i ∈ s, z.2 (r z.1 i) = η i} =
      ∫⁻ e, if Consistent s (r e) η then p ^ (s.image (r e)).card else 0 ∂μ := by
  have hC : MeasurableSet {x : I → A | ∀ i ∈ s, x i = η i} :=
    MeasurableSet.pi s.countable_toSet (fun _ _ => measurableSet_singleton _)
  have hm : MeasurableSet {z : E × (J → A) |
      ∀ i ∈ s, z.2 (r z.1 i) = η i} := (measurable_select r hr) hC
  rw [Measure.prod_apply hm]
  apply lintegral_congr
  intro e
  exact finite_cylinder ν p hmass s (r e) η

theorem map_select_of_indep {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (ν : Measure A) [IsProbabilityMeasure ν]
    (Z : Ω → E) (U : Ω → J → A) (hZ : Measurable Z) (hU : Measurable U)
    (hind : IndepFun Z U P)
    (hlaw : P.map U = Measure.infinitePi (fun _ : J => ν))
    (r : E → I → J) (hr : ∀ i, Measurable (fun e => r e i))
    (hinj : ∀ᵐ e ∂P.map Z, Function.Injective (r e)) :
    P.map (fun ω => (Z ω, fun i => U ω (r (Z ω) i))) =
      (P.map Z).prod (Measure.infinitePi (fun _ : I => ν)) := by
  have hT := (measurePreserving_select (P.map Z) ν r hr hinj).measurable
  change P.map ((fun z : E × (J → A) =>
    (z.1, fun i => z.2 (r z.1 i))) ∘ (fun ω => (Z ω, U ω))) = _
  rw [← Measure.map_map hT (hZ.prodMk hU),
    hind.map_prod_eq_prod_map_map hZ.aemeasurable hU.aemeasurable, hlaw]
  exact map_select (P.map Z) ν r hr hinj

end Problem367.RandomIndexSampling

end

end OAI
