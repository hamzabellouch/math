import OAI.Probability.FreeIsing.Estimates.CountableProjective

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Finset Function
namespace Problem367.CountableProjective

variable {ι κ A : Type*} [MeasurableSpace A]

private def pullFinite (e : ι ↪ κ) (I : Finset ι) (x : I.map e → A) (i : I) : A :=
  x ⟨e i, mem_map.mpr ⟨i, i.property, rfl⟩⟩

private lemma measurable_pullFinite (e : ι ↪ κ) (I : Finset ι) :
    Measurable (pullFinite (A := A) e I) := by
  exact Measurable.of_eval fun _ => measurable_pi_apply _

omit [MeasurableSpace A] in
private lemma injective_pullFinite (e : ι ↪ κ) (I : Finset ι) :
    Injective (pullFinite (A := A) e I) := by
  intro x y h
  funext j
  obtain ⟨i, hi, hij⟩ := mem_map.mp j.property
  have he : j = ⟨e i, mem_map.mpr ⟨i, hi, rfl⟩⟩ := Subtype.ext hij.symm
  subst j
  exact congrFun h ⟨i, hi⟩

private def pullFamily (e : ι ↪ κ)
    (μ : (I : Finset κ) → Measure (I → A)) (I : Finset ι) : Measure (I → A) :=
  (μ (I.map e)).map (pullFinite e I)

private lemma projective_pullFamily (e : ι ↪ κ)
    (μ : (I : Finset κ) → Measure (I → A)) (hμ : IsProjectiveMeasureFamily (α := fun _ => A) μ) :
    IsProjectiveMeasureFamily (α := fun _ => A) (pullFamily e μ) := by
  intro I J hJI
  dsimp [pullFamily]
  rw [hμ (I.map e) (J.map e) (map_subset_map.mpr hJI)]
  rw [Measure.map_map (measurable_pullFinite _ _) (Finset.measurable_restrict₂ _),
    Measure.map_map (Finset.measurable_restrict₂ (X := fun _ => A) hJI) (measurable_pullFinite _ _)]
  rfl

theorem exists_projective_limit_of_equiv_nat [StandardBorelSpace A] [Nonempty A]
    (e : ℕ ≃ ι) (μ : (I : Finset ι) → Measure (I → A))
    [∀ I, IsProbabilityMeasure (μ I)] (hμ : IsProjectiveMeasureFamily (α := fun _ => A) μ) :
    ∃ ν : Measure (ι → A), IsProbabilityMeasure ν ∧ IsProjectiveLimit (α := fun _ => A) ν μ := by
  classical
  let μ' := pullFamily e.toEmbedding μ
  let (I : Finset ℕ) : IsProbabilityMeasure (μ' I) := by
    dsimp [μ', pullFamily]
    infer_instance
  obtain ⟨ν', hν', hmarg⟩ := exists_nat_projective_limit (X := fun _ => A) μ' (projective_pullFamily _ _ hμ)
  let := hν'
  let f : (ℕ → A) → (ι → A) := fun x i => x (e.symm i)
  have hf : Measurable f := by fun_prop
  let ν := ν'.map f
  refine ⟨ν, inferInstance, ?_⟩
  have hmap (I : Finset ℕ) : ν.map (I.map e.toEmbedding).restrict = μ (I.map e.toEmbedding) := by
    apply (measurable_pullFinite (A := A) e.toEmbedding I).measurableEmbedding
      (injective_pullFinite _ _) |>.map_injective
    rw [Measure.map_map (measurable_pullFinite _ _) (Finset.measurable_restrict _)]
    change (ν'.map f).map _ = _
    rw [Measure.map_map ((measurable_pullFinite _ _).comp (Finset.measurable_restrict _)) hf]
    have heq : pullFinite (A := A) e.toEmbedding I ∘ (I.map e.toEmbedding).restrict ∘ f = I.restrict := by
      funext x i
      simp [pullFinite, f]
    rw [Function.comp_assoc, heq]
    exact hmarg I
  intro I
  have hi : (I.map e.symm.toEmbedding).map e.toEmbedding = I := by
    ext i
    simp only [mem_map]
    constructor
    · rintro ⟨j, ⟨k, hk, rfl⟩, rfl⟩
      simpa using hk
    · intro hi
      refine ⟨e.symm i, ⟨i, hi, rfl⟩, e.apply_symm_apply i⟩
  have H := hmap (I.map e.symm.toEmbedding)
  rw [hi] at H
  exact H

theorem exists_countable_projective_limit [Countable ι] [StandardBorelSpace A] [Nonempty A]
    (μ : (I : Finset ι) → Measure (I → A))
    [∀ I, IsProbabilityMeasure (μ I)] (hμ : IsProjectiveMeasureFamily (α := fun _ => A) μ) :
    ∃ ν : Measure (ι → A), IsProbabilityMeasure ν ∧ IsProjectiveLimit (α := fun _ => A) ν μ := by
  classical
  cases finite_or_infinite ι with
  | inl h =>
    let := Fintype.ofFinite ι
    let g : (↑(Finset.univ : Finset ι) → A) → (ι → A) := fun x i => x ⟨i, mem_univ i⟩
    have hg : Measurable g := by fun_prop
    refine ⟨(μ univ).map g, inferInstance, ?_⟩
    intro I
    rw [Measure.map_map (Finset.measurable_restrict _) hg]
    exact (hμ univ I (subset_univ I)).symm
  | inr h =>
    obtain ⟨e⟩ : Nonempty (ℕ ≃ ι) := nonempty_equiv_of_countable
    exact exists_projective_limit_of_equiv_nat e μ hμ

private lemma marginal_map_extension [StandardBorelSpace A]
    (e : κ ↪ ι) (μ : (I : Finset ι) → Measure (I → A))
    (ν : Measure (κ → A)) (hmarg : IsProjectiveLimit (α := fun _ => A) ν (pullFamily e μ))
    (f : (κ → A) → (ι → A)) (hf : Measurable f)
    (hleft : ∀ x i, f x (e i) = x i) (I : Finset κ) :
    (ν.map f).map (I.map e).restrict = μ (I.map e) := by
  apply (measurable_pullFinite (A := A) e I).measurableEmbedding
    (injective_pullFinite _ _) |>.map_injective
  rw [Measure.map_map (measurable_pullFinite _ _) (Finset.measurable_restrict _),
    Measure.map_map ((measurable_pullFinite _ _).comp (Finset.measurable_restrict _)) hf]
  have heq : (pullFinite (A := A) e I ∘ (I.map e).restrict) ∘ f = I.restrict := by
    funext x i
    exact hleft x i
  rw [heq]
  exact hmarg I

theorem exists_measure_for_countable_marginals [StandardBorelSpace A] [Nonempty A]
    (μ : (I : Finset ι) → Measure (I → A))
    [∀ I, IsProbabilityMeasure (μ I)] (hμ : IsProjectiveMeasureFamily (α := fun _ => A) μ)
    (I : ℕ → Finset ι) :
    ∃ ν : Measure (ι → A), IsProbabilityMeasure ν ∧ ∀ n, ν.map (I n).restrict = μ (I n) := by
  classical
  let S : Set ι := ⋃ n, (I n : Set ι)
  have hS : S.Countable := Set.countable_iUnion fun n => (I n).countable_toSet
  let : Countable S := hS.to_subtype
  let e : S ↪ ι := Function.Embedding.subtype _
  let μ' := pullFamily e μ
  let (J : Finset S) : IsProbabilityMeasure (μ' J) := by
    dsimp [μ', pullFamily]
    infer_instance
  obtain ⟨ν', hν', hmarg⟩ := exists_countable_projective_limit μ' (projective_pullFamily _ _ hμ)
  let := hν'
  let a : A := Classical.choice inferInstance
  let f : (S → A) → (ι → A) := fun x i => if hi : i ∈ S then x ⟨i, hi⟩ else a
  have hf : Measurable f := by
    apply Measurable.of_eval
    intro i
    by_cases hi : i ∈ S
    · simpa only [f, dite_eq_left hi] using (measurable_pi_apply (⟨i, hi⟩ : S))
    · simpa only [f, dite_eq_right hi] using (measurable_const : Measurable (fun _ : S → A => a))
  have hleft (x : S → A) (i : S) : f x (e i) = x i := by simp [f, e, i.property]
  refine ⟨ν'.map f, inferInstance, ?_⟩
  intro n
  have hn (i : ι) (hi : i ∈ I n) : i ∈ S := Set.mem_iUnion.mpr ⟨n, hi⟩
  have hj : ((I n).subtype (· ∈ S)).map e = I n := Finset.subtype_map_of_mem hn
  have H := marginal_map_extension e μ ν' hmarg f hf hleft ((I n).subtype (· ∈ S))
  rw [hj] at H
  exact H

private lemma projectiveContent_tendsto_zero [StandardBorelSpace A] [Nonempty A]
    (μ : (I : Finset ι) → Measure (I → A))
    [∀ I, IsProbabilityMeasure (μ I)] (hμ : IsProjectiveMeasureFamily (α := fun _ => A) μ)
    (s : ℕ → Set (ι → A)) (hs : ∀ n, s n ∈ measurableCylinders (fun _ : ι => A))
    (hanti : Antitone s) (hempty : ⋂ n, s n = ∅) :
    Filter.Tendsto (fun n => projectiveFamilyContent hμ (s n)) Filter.atTop (nhds 0) := by
  classical
  let I n := measurableCylinders.finset (hs n)
  obtain ⟨ν, hν, hmarg⟩ := exists_measure_for_countable_marginals μ hμ I
  let := hν
  have heq (n : ℕ) : projectiveFamilyContent hμ (s n) = ν (s n) := by
    rw [measurableCylinders.eq_cylinder (hs n),
      projectiveFamilyContent_cylinder hμ (measurableCylinders.measurableSet (hs n))]
    rw [cylinder, ← Measure.map_apply (Finset.measurable_restrict _)
      (measurableCylinders.measurableSet (hs n)), hmarg n]
  simp_rw [heq]
  have hlim := tendsto_measure_iInter_atTop
    (fun n => (MeasurableSet.of_mem_measurableCylinders (hs n)).nullMeasurableSet (μ := ν))
    hanti ⟨0, measure_ne_top _ _⟩
  simpa only [hempty, measure_empty, Function.comp_def] using hlim

theorem exists_projective_limit [StandardBorelSpace A] [Nonempty A]
    (μ : (I : Finset ι) → Measure (I → A))
    [∀ I, IsProbabilityMeasure (μ I)] (hμ : IsProjectiveMeasureFamily (α := fun _ => A) μ) :
    ∃ ν : Measure (ι → A), IsProbabilityMeasure ν ∧ IsProjectiveLimit (α := fun _ => A) ν μ := by
  have hadd : (projectiveFamilyContent hμ).IsSigmaSubadditive := by
    refine isSigmaSubadditive_of_addContent_iUnion_eq_tsum
      isSetRing_measurableCylinders (fun f hf hu hd => ?_)
    refine addContent_iUnion_eq_sum_of_tendsto_zero isSetRing_measurableCylinders
      (projectiveFamilyContent hμ) (fun _ _ => projectiveFamilyContent_ne_top hμ) ?_ hf hu hd
    exact fun s hs ha he => projectiveContent_tendsto_zero μ hμ s hs ha he
  let ν : Measure (ι → A) := (projectiveFamilyContent hμ).measure
    isSetSemiring_measurableCylinders generateFrom_measurableCylinders.ge hadd
  have hlimit : IsProjectiveLimit (α := fun _ => A) ν μ := by
    intro I
    ext t ht
    rw [Measure.map_apply (Finset.measurable_restrict _) ht]
    change ν (cylinder I t) = _
    dsimp [ν]
    rw [AddContent.measure_eq _ _ generateFrom_measurableCylinders.symm _
      (cylinder_mem_measurableCylinders (α := fun _ : ι => A) I t ht), projectiveFamilyContent_cylinder hμ ht]
  exact ⟨ν, hlimit.isProbabilityMeasure, hlimit⟩

end Problem367.CountableProjective

end

end OAI
