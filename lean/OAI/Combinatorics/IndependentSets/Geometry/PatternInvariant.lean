import Mathlib
import OAI.Combinatorics.IndependentSets.Reduction.ListIndex
import OAI.Combinatorics.IndependentSets.Reduction.ExtendPartialIso

namespace OAI

namespace LargeIndependentSets
open MeasureTheory Set

def PatternInvariant {s d : ℕ} (μ : Measure (ListPattern s d ℚ)) : Prop :=
  ∀ e : ℚ ≃o ℚ, Measure.map (ListPattern.restrict e.toOrderEmbedding) μ = μ

lemma occupied_measurable {s d : ℕ} (a : ListSlot s d ℚ) :
    MeasurableSet {C : ListPattern s d ℚ | C.val a a = true} :=
  (isClosed_eq (patternEval_continuous a a) continuous_const).measurableSet

theorem invariant_pattern_cut_in_list {s d : ℕ} (μ : Measure (ListPattern s d ℚ))
    [IsFiniteMeasure μ] (hinv : PatternInvariant μ) (a : ListSlot s d ℚ) :
    μ {C | C.val a a = true ∧
      patternCut C a ∉ ((↑a.1.val : Set ℚ).image ((↑) : ℚ → ℝ))} = 0 := by
  classical
  let E : Set (ListPattern s d ℚ) := {C | C.val a a = true}
  let ν : Measure ℝ := Measure.map (fun C => patternCut C a) (μ.restrict E)
  have hCDF (x y : ℚ) (hxy : x < y) (hx : x ∉ a.1.val) (hy : y ∉ a.1.val)
      (hcut : ∀ i ∈ a.1.val, i < x ↔ i < y) : ν (Iic (x : ℝ)) = ν (Iic (y : ℝ)) := by
    obtain ⟨e, hexy, hefix⟩ := rational_automorphism_fixing a.1.val x y hx hy hcut
    have hea := ListSlot.map_eq_self e a hefix
    let F : Set (ListPattern s d ℚ) :=
      (fun C => patternCut C a) ⁻¹' Iic (x : ℝ) ∩ E
    have hF : MeasurableSet F :=
      ((patternCut_measurable a) measurableSet_Iic).inter (occupied_measurable a)
    have hh := congrArg (fun τ : Measure (ListPattern s d ℚ) => τ F) (hinv e)
    rw [Measure.map_apply (ListPattern.continuous_restrict e.toOrderEmbedding).measurable hF] at hh
    have hfpre : (ListPattern.restrict e.toOrderEmbedding) ⁻¹' F =
        (fun C => patternCut C a) ⁻¹' Iic (y : ℝ) ∩ E := by
      ext C
      change (patternCut (ListPattern.restrict e.toOrderEmbedding C) a ≤ (x : ℝ) ∧
        C.val (ListSlot.map e.toEmbedding a) (ListSlot.map e.toEmbedding a) = true) ↔
        (patternCut C a ≤ (y : ℝ) ∧ C.val a a = true)
      rw [patternCut_restrict_CDF, hea, hexy]
    rw [hfpre] at hh
    dsimp only [ν]
    rw [Measure.map_apply (patternCut_measurable a) measurableSet_Iic,
      Measure.map_apply (patternCut_measurable a) measurableSet_Iic,
      Measure.restrict_apply ((patternCut_measurable a) measurableSet_Iic),
      Measure.restrict_apply ((patternCut_measurable a) measurableSet_Iic)]
    exact hh.symm
  have hz := invariant_cut_support_open a.1.val ν hCDF
  have hcomp : MeasurableSet (((↑a.1.val : Set ℚ).image ((↑) : ℚ → ℝ))ᶜ) :=
    (a.1.val.finite_toSet.image _).measurableSet.compl
  dsimp only [ν] at hz
  rw [Measure.map_apply (patternCut_measurable a) hcomp,
    Measure.restrict_apply ((patternCut_measurable a) hcomp)] at hz
  convert hz using 2
  ext C
  change (_ ∧ _) ↔ (_ ∧ _)
  tauto

def GloballyAligned {s d : ℕ} (C : ListPattern s d ℚ) : Prop :=
  ∀ a, C.val a a = true → ∃ i : ℚ, ∀ b, C.val a b = true → i ∈ b.1.val

theorem invariant_pattern_globally_aligned {s d : ℕ}
    (μ : Measure (ListPattern s d ℚ)) [IsFiniteMeasure μ] (hinv : PatternInvariant μ) :
    ∀ᵐ C ∂μ, GloballyAligned C := by
  have ha (a : ListSlot s d ℚ) : ∀ᵐ C ∂μ, C.val a a = true →
      patternCut C a ∈ ((↑a.1.val : Set ℚ).image ((↑) : ℚ → ℝ)) := by
    apply ae_iff.mpr
    convert invariant_pattern_cut_in_list μ hinv a using 2
    ext C
    exact Classical.not_imp
  have hall : ∀ᵐ C ∂μ, ∀ a : ListSlot s d ℚ, C.val a a = true →
      patternCut C a ∈ ((↑a.1.val : Set ℚ).image ((↑) : ℚ → ℝ)) :=
    ae_all_iff.mpr ha
  filter_upwards [hall] with C hC
  intro a haa
  obtain ⟨i, hi, hic⟩ := hC a haa
  refine ⟨i, ?_⟩
  intro b hab
  have hbb : C.val b b = true := C.occupied_of_eq (C.property.1 a b hab)
  obtain ⟨j, hj, hjc⟩ := hC b hbb
  have hij : (i : ℝ) = (j : ℝ) := hic.trans ((patternCut_eq_of_eq C a b hab).trans hjc.symm)
  have hij' : i = j := by exact_mod_cast hij
  exact hij' ▸ hj

def GoodPatternOn {s d : ℕ} {X : Type*} [LinearOrder X]
    (C : ListPattern s d X) (B : Finset X) : Prop :=
  ∀ a, a.1.val ⊆ B → C.val a a = true → ∃ i ∈ B,
    ∀ b, b.1.val ⊆ B → C.val a b = true → i ∈ b.1.val

lemma GloballyAligned.goodOn {s d : ℕ} (C : ListPattern s d ℚ)
    (h : GloballyAligned C) (B : Finset ℚ) : GoodPatternOn C B := by
  intro a ha haa
  obtain ⟨i, hi⟩ := h a haa
  exact ⟨i, ha (hi a haa), fun b _ hab => hi b hab⟩

theorem invariant_pattern_no_bad_sets {s d : ℕ}
    (μ : Measure (ListPattern s d ℚ)) [IsFiniteMeasure μ] (hinv : PatternInvariant μ)
    (B : Finset ℚ) : μ {C | ¬GoodPatternOn C B} = 0 := by
  have h : ∀ᵐ C ∂μ, GoodPatternOn C B :=
    (invariant_pattern_globally_aligned μ hinv).mono (fun C h => h.goodOn C B)
  exact ae_iff.mp h

noncomputable def ListIndex.inside {s : ℕ} {X : Type*} [LinearOrder X]
    (B : Finset X) (I : ListIndex s X) (h : I.val ⊆ B) : ListIndex s B := by
  classical
  refine ⟨I.val.subtype (· ∈ B), ?_, ?_⟩
  · obtain ⟨x, hx⟩ := I.property.1
    exact ⟨⟨x, h hx⟩, Finset.mem_subtype.mpr hx⟩
  · exact (Finset.card_subtype _ _).trans_le
      ((Finset.card_filter_le _ _).trans I.property.2)

lemma ListIndex.map_inside {s : ℕ} {X : Type*} [LinearOrder X]
    (B : Finset X) (I : ListIndex s X) (h : I.val ⊆ B) :
    ListIndex.map (Function.Embedding.subtype (· ∈ B)) (I.inside B h) = I := by
  classical
  apply Subtype.ext
  exact Finset.subtype_map_of_mem (fun x hx => h hx)

noncomputable def ListSlot.inside {s d : ℕ} {X : Type*} [LinearOrder X]
    (B : Finset X) (a : ListSlot s d X) (h : a.1.val ⊆ B) : ListSlot s d B :=
  (a.1.inside B h, a.2)

lemma ListSlot.map_inside {s d : ℕ} {X : Type*} [LinearOrder X]
    (B : Finset X) (a : ListSlot s d X) (h : a.1.val ⊆ B) :
    ListSlot.map (Function.Embedding.subtype (· ∈ B)) (a.inside B h) = a := by
  exact Prod.ext (ListIndex.map_inside B a.1 h) rfl

noncomputable def liftData {s d : ℕ} {X : Type*} [LinearOrder X]
    (B : Finset X) (C : ListPattern s d B) : EqualityData s d X := by
  classical
  exact fun a b => if ha : a.1.val ⊆ B then
    if hb : b.1.val ⊆ B then C.val (a.inside B ha) (b.inside B hb) else false else false

lemma liftData_true_iff {s d : ℕ} {X : Type*} [LinearOrder X]
    (B : Finset X) (C : ListPattern s d B) (a b : ListSlot s d X) :
    liftData B C a b = true ↔ ∃ ha : a.1.val ⊆ B, ∃ hb : b.1.val ⊆ B,
      C.val (a.inside B ha) (b.inside B hb) = true := by
  classical
  simp only [liftData]
  split_ifs <;> simp_all

noncomputable def ListPattern.lift {s d : ℕ} {X : Type*} [LinearOrder X]
    (B : Finset X) (C : ListPattern s d B) : ListPattern s d X := by
  classical
  refine ⟨liftData B C, ?_, ?_, ?_, ?_⟩
  · intro a b h
    obtain ⟨ha, hb, hab⟩ := (liftData_true_iff B C a b).mp h
    exact (liftData_true_iff B C b a).mpr ⟨hb, ha, C.property.1 _ _ hab⟩
  · intro a b c hab hbc
    obtain ⟨ha, hb, hab⟩ := (liftData_true_iff B C a b).mp hab
    obtain ⟨_, hc, hbc⟩ := (liftData_true_iff B C b c).mp hbc
    exact (liftData_true_iff B C a c).mpr ⟨ha, hc, C.property.2.1 _ _ _ hab hbc⟩
  · intro a b hab habI
    obtain ⟨ha, hb, hab⟩ := (liftData_true_iff B C a b).mp hab
    apply C.property.2.2.1 _ _ hab
    change ListIndex.inside B a.1 ha = ListIndex.inside B b.1 hb
    apply Subtype.ext
    change a.1.val.subtype (· ∈ B) = b.1.val.subtype (· ∈ B)
    rw [congrArg Subtype.val habI]
  · intro a b hsep
    apply Bool.eq_false_iff.mpr
    intro hab
    obtain ⟨ha, hb, hab⟩ := (liftData_true_iff B C a b).mp hab
    have hf := C.property.2.2.2 (a.inside B ha) (b.inside B hb) (by
      intro x hx y hy
      exact hsep x.val (Finset.mem_subtype.mp hx) y.val (Finset.mem_subtype.mp hy))
    exact Bool.false_ne_true (hf.symm.trans hab)

lemma ListSlot.inside_map {s d : ℕ} {X : Type*} [LinearOrder X]
    (B : Finset X) (a : ListSlot s d B)
    (h : (ListSlot.map (Function.Embedding.subtype (· ∈ B)) a).1.val ⊆ B) :
    (ListSlot.map (Function.Embedding.subtype (· ∈ B)) a).inside B h = a := by
  apply ListSlot.map_injective (Function.Embedding.subtype (· ∈ B))
  exact ListSlot.map_inside B _ h

lemma ListPattern.restrict_lift {s d : ℕ} {X : Type*} [LinearOrder X]
    (B : Finset X) (C : ListPattern s d B) :
    ListPattern.restrict (OrderEmbedding.subtype (· ∈ B)) (C.lift B) = C := by
  classical
  apply Subtype.ext
  funext a b
  have h (a : ListSlot s d B) :
      (ListSlot.map (Function.Embedding.subtype (· ∈ B)) a).1.val ⊆ B := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_map.mp hx
    exact y.property
  change liftData B C (ListSlot.map (Function.Embedding.subtype (· ∈ B)) a)
    (ListSlot.map (Function.Embedding.subtype (· ∈ B)) b) = _
  simp only [liftData, dite_eq_left (h a), dite_eq_left (h b), ListSlot.inside_map]

lemma ListIndex.map_id {s : ℕ} {X : Type*} (I : ListIndex s X) :
    ListIndex.map (Function.Embedding.refl X) I = I := by
  apply Subtype.ext
  exact Finset.map_refl

lemma ListSlot.map_id {s d : ℕ} {X : Type*} (a : ListSlot s d X) :
    ListSlot.map (Function.Embedding.refl X) a = a :=
  Prod.ext (ListIndex.map_id a.1) rfl

lemma ListSlot.map_comp {s d : ℕ} {X Y Z : Type*} (e : X ↪ Y) (f : Y ↪ Z)
    (a : ListSlot s d X) :
    ListSlot.map f (ListSlot.map e a) = ListSlot.map (e.trans f) a := by
  apply Prod.ext
  · apply Subtype.ext
    exact Finset.map_map _ _ _
  · rfl

lemma ListPattern.restrict_id {s d : ℕ} {X : Type*} [LinearOrder X]
    (C : ListPattern s d X) : ListPattern.restrict ((OrderIso.refl X).toOrderEmbedding) C = C := by
  apply Subtype.ext
  funext a b
  change C.val (ListSlot.map (Function.Embedding.refl X) a)
    (ListSlot.map (Function.Embedding.refl X) b) = C.val a b
  rw [ListSlot.map_id, ListSlot.map_id]

lemma ListPattern.restrict_comp {s d : ℕ} {X Y Z : Type*}
    [LinearOrder X] [LinearOrder Y] [LinearOrder Z] (e : X ↪o Y) (f : Y ↪o Z)
    (C : ListPattern s d Z) :
    (C.restrict f).restrict e = C.restrict (e.trans f) := by
  apply Subtype.ext
  funext a b
  change C.val (ListSlot.map f.toEmbedding (ListSlot.map e.toEmbedding a))
    (ListSlot.map f.toEmbedding (ListSlot.map e.toEmbedding b)) = _
  rw [ListSlot.map_comp, ListSlot.map_comp]
  rfl

noncomputable def ListPattern.extendFin {s d n : ℕ} {X : Type*} [LinearOrder X]
    (B : Finset X) (h : B.card = n) (C : ListPattern s d (Fin n)) : ListPattern s d X :=
  (C.restrict (B.orderIsoOfFin h).symm.toOrderEmbedding).lift B

lemma ListPattern.restrict_extendFin {s d n : ℕ} {X : Type*} [LinearOrder X]
    (B : Finset X) (h : B.card = n) (C : ListPattern s d (Fin n)) :
    (C.extendFin B h).restrict (B.orderEmbOfFin h) = C := by
  change ((C.restrict (B.orderIsoOfFin h).symm.toOrderEmbedding).lift B).restrict
    ((B.orderIsoOfFin h).toOrderEmbedding.trans (OrderEmbedding.subtype (· ∈ B))) = C
  rw [← ListPattern.restrict_comp, ListPattern.restrict_lift, ListPattern.restrict_comp]
  have he : (B.orderIsoOfFin h).toOrderEmbedding.trans
      (B.orderIsoOfFin h).symm.toOrderEmbedding = (OrderIso.refl (Fin n)).toOrderEmbedding := by
    apply DFunLike.ext; intro x; exact (B.orderIsoOfFin h).symm_apply_apply x
  rw [he, ListPattern.restrict_id]

lemma GloballyAligned.good_full_restrict {s d n : ℕ} (C : ListPattern s d ℚ)
    (hC : GloballyAligned C) (e : Fin n ↪o ℚ) :
    GoodPatternOn (C.restrict e) Finset.univ := by
  classical
  intro a ha haa
  obtain ⟨i, hi⟩ := hC (ListSlot.map e.toEmbedding a) haa
  obtain ⟨j, hj, hji⟩ := Finset.mem_map.mp (hi (ListSlot.map e.toEmbedding a) haa)
  refine ⟨j, Finset.mem_univ _, ?_⟩
  intro b _ hab
  obtain ⟨k, hk, hki⟩ := Finset.mem_map.mp (hi (ListSlot.map e.toEmbedding b) hab)
  have hjk : j = k := e.injective (hji.trans hki.symm)
  exact hjk ▸ hk

lemma isClopen_finite_pattern_event {s d n : ℕ} (E : Set (ListPattern s d (Fin n))) :
    IsClopen E := isClopen_discrete E

lemma isClopen_bad_restrict {s d n : ℕ} {X : Type*} [LinearOrder X]
    (e : Fin n ↪o X) :
    IsClopen {C : ListPattern s d X | ¬GoodPatternOn (C.restrict e) Finset.univ} :=
  (isClopen_finite_pattern_event {D | ¬GoodPatternOn D Finset.univ}).preimage
    (ListPattern.continuous_restrict e)

lemma ListPattern.measurable_restrict {s d : ℕ} {X Y : Type*}
    [LinearOrder X] [LinearOrder Y] (e : X ↪o Y) :
    Measurable (ListPattern.restrict (s := s) (d := d) e) := by
  apply Measurable.subtype_mk
  apply Measurable.of_eval; intro a
  apply Measurable.of_eval; intro b
  exact (measurable_pi_apply (ListSlot.map e.toEmbedding b)).comp
    ((measurable_pi_apply (ListSlot.map e.toEmbedding a) :
      Measurable (fun C : EqualityData s d Y => C (ListSlot.map e.toEmbedding a))).comp
      measurable_subtype_coe)

noncomputable def restrictionLaw {s d : ℕ} {X Y : Type*}
    [LinearOrder X] [LinearOrder Y] (e : X ↪o Y)
    (μ : ProbabilityMeasure (ListPattern s d Y)) : ProbabilityMeasure (ListPattern s d X) :=
  μ.map (ListPattern.restrict e)

lemma restrictionLaw_comp {s d : ℕ} {X Y Z : Type*}
    [LinearOrder X] [LinearOrder Y] [LinearOrder Z] (e : X ↪o Y) (f : Y ↪o Z)
    (μ : ProbabilityMeasure (ListPattern s d Z)) :
    restrictionLaw e (restrictionLaw f μ) = restrictionLaw (e.trans f) μ := by
  apply ProbabilityMeasure.toMeasure_injective
  change Measure.map (ListPattern.restrict e) (Measure.map (ListPattern.restrict f) (μ : Measure (ListPattern s d Z))) = _
  rw [Measure.map_map (ListPattern.measurable_restrict e) (ListPattern.measurable_restrict f)]
  congr 1
  funext C
  exact ListPattern.restrict_comp e f C

lemma restrictionLaw_id {s d : ℕ} {X : Type*} [LinearOrder X]
    (μ : ProbabilityMeasure (ListPattern s d X)) :
    restrictionLaw (OrderIso.refl X).toOrderEmbedding μ = μ := by
  apply ProbabilityMeasure.toMeasure_injective
  change Measure.map _ _ = _
  have he : ListPattern.restrict (s := s) (d := d) (OrderIso.refl X).toOrderEmbedding = id := by
    funext C; exact ListPattern.restrict_id C
  rw [he, Measure.map_id]

lemma finite_laws_invariant {s d : ℕ}
    (μ : ProbabilityMeasure (ListPattern s d ℚ))
    (h : ∀ n (e f : Fin n ↪o ℚ), restrictionLaw e μ = restrictionLaw f μ) :
    PatternInvariant (μ : Measure (ListPattern s d ℚ)) := by
  classical
  intro g
  let encode : ListPattern s d ℚ → (ListSlot s d ℚ × ListSlot s d ℚ → Bool) :=
    fun C ab => C.val ab.1 ab.2
  have hm : MeasurableEmbedding encode :=
    (MeasurableEquiv.curry (ListSlot s d ℚ) (ListSlot s d ℚ) Bool).symm.measurableEmbedding.comp
      (MeasurableEmbedding.subtype_coe (isClosed_isPattern s d ℚ).measurableSet)
  apply hm.map_injective
  rw [Measure.map_map hm.measurable (ListPattern.measurable_restrict g.toOrderEmbedding)]
  apply (ProbabilityTheory.map_eq_iff_forall_finset_map_restrict_eq
    (hm.measurable.comp (ListPattern.measurable_restrict g.toOrderEmbedding)).aemeasurable
    hm.measurable.aemeasurable).mpr
  intro J
  let B : Finset ℚ := J.biUnion (fun ab => ab.1.1.val ∪ ab.2.1.val)
  have hB (ab : J) : ab.val.1.1.val ⊆ B ∧ ab.val.2.1.val ⊆ B := by
    constructor
    · intro x hx
      exact Finset.mem_biUnion.mpr ⟨ab.val, ab.property, Finset.mem_union_left _ hx⟩
    · intro x hx
      exact Finset.mem_biUnion.mpr ⟨ab.val, ab.property, Finset.mem_union_right _ hx⟩
  let e : B ↪o ℚ := OrderEmbedding.subtype (· ∈ B)
  let u : Fin B.card ≃o B := B.orderIsoOfFin rfl
  have hfin := h B.card (u.toOrderEmbedding.trans (e.trans g.toOrderEmbedding))
    (u.toOrderEmbedding.trans e)
  have hsub := congrArg (restrictionLaw u.symm.toOrderEmbedding) hfin
  simp only [restrictionLaw_comp] at hsub
  have he1 : u.symm.toOrderEmbedding.trans (u.toOrderEmbedding.trans (e.trans g.toOrderEmbedding)) =
      e.trans g.toOrderEmbedding := by
    apply DFunLike.ext; intro x; exact congrArg (e.trans g.toOrderEmbedding) (u.apply_symm_apply x)
  have he2 : u.symm.toOrderEmbedding.trans (u.toOrderEmbedding.trans e) = e := by
    apply DFunLike.ext; intro x; exact congrArg e (u.apply_symm_apply x)
  rw [he1, he2] at hsub
  let F : ListPattern s d B → (J → Bool) := fun C ab =>
    C.val (ab.val.1.inside B (hB ab).1) (ab.val.2.inside B (hB ab).2)
  have hFm : Measurable F := (continuous_of_discreteTopology : Continuous F).measurable
  have hmap := congrArg (fun ν : ProbabilityMeasure (ListPattern s d B) =>
    Measure.map F (ν : Measure (ListPattern s d B))) hsub
  change Measure.map F (Measure.map _ _) = Measure.map F (Measure.map _ _) at hmap
  rw [Measure.map_map hFm (ListPattern.measurable_restrict _),
    Measure.map_map hFm (ListPattern.measurable_restrict _)] at hmap
  convert hmap using 1 <;> congr 1 <;> funext C ab
  · change C.val (ListSlot.map g.toEmbedding ab.val.1) (ListSlot.map g.toEmbedding ab.val.2) =
      C.val (ListSlot.map (e.trans g.toOrderEmbedding).toEmbedding
        (ab.val.1.inside B (hB ab).1))
        (ListSlot.map (e.trans g.toOrderEmbedding).toEmbedding (ab.val.2.inside B (hB ab).2))
    change C.val (ListSlot.map g.toEmbedding ab.val.1) (ListSlot.map g.toEmbedding ab.val.2) =
      C.val (ListSlot.map ((Function.Embedding.subtype (· ∈ B)).trans g.toEmbedding)
        (ab.val.1.inside B (hB ab).1))
        (ListSlot.map ((Function.Embedding.subtype (· ∈ B)).trans g.toEmbedding)
          (ab.val.2.inside B (hB ab).2))
    rw [← ListSlot.map_comp, ← ListSlot.map_comp, ListSlot.map_inside, ListSlot.map_inside]
  · change C.val ab.val.1 ab.val.2 =
      C.val (ListSlot.map (Function.Embedding.subtype (· ∈ B))
        (ab.val.1.inside B (hB ab).1))
        (ListSlot.map (Function.Embedding.subtype (· ∈ B)) (ab.val.2.inside B (hB ab).2))
    rw [ListSlot.map_inside, ListSlot.map_inside]

open Filter
open scoped Topology

instance patternMetrizable (s d : ℕ) (X : Type*) [LinearOrder X] [Countable X] :
    TopologicalSpace.MetrizableSpace (ListPattern s d X) := by
  have : TopologicalSpace.MetrizableSpace (EqualityData s d X) := inferInstance
  exact TopologicalSpace.MetrizableSpace.subtype {C : EqualityData s d X | IsPattern C}

instance patternSecondCountable (s d : ℕ) (X : Type*) [LinearOrder X] [Countable X] :
    SecondCountableTopology (ListPattern s d X) := by
  have : SecondCountableTopology (EqualityData s d X) := inferInstance
  infer_instance

noncomputable instance finitePatternLawMetric (s d n : ℕ) :
    MetricSpace (ProbabilityMeasure (ListPattern s d (Fin n))) :=
  by
    have := MeasureTheory.instMetrizableSpaceProbabilityMeasure (ListPattern s d (Fin n))
    exact TopologicalSpace.metrizableSpaceMetric _

lemma continuous_restrictionLaw {s d n : ℕ} (e : Fin n ↪o ℚ) :
    Continuous (restrictionLaw (s := s) (d := d) e) :=
  ProbabilityMeasure.continuous_map (ListPattern.continuous_restrict e)

theorem no_asymptotically_invariant_bad_sequence {s d : ℕ} {ξ : ℝ} (hξ : 0 < ξ)
    (seq : ℕ → ProbabilityMeasure (ListPattern s d ℚ))
    (hhom : ∀ n (e f : Fin n ↪o ℚ), ∀ᶠ k in atTop,
      dist (restrictionLaw e (seq k)) (restrictionLaw f (seq k)) ≤ 1 / ((k : ℝ) + 1))
    (e₀ : Fin s ↪o ℚ)
    (hbad : ∀ᶠ k in atTop,
      ξ ≤ ((seq k) {C | ¬GoodPatternOn (C.restrict e₀) Finset.univ} : ℝ)) : False := by
  obtain ⟨μ, φ, hφ, hlim⟩ := CompactSpace.tendsto_subseq seq
  have hinv : PatternInvariant (μ : Measure (ListPattern s d ℚ)) := by
    apply finite_laws_invariant μ
    intro n e f
    have he := (continuous_restrictionLaw e).tendsto μ |>.comp hlim
    have hf := (continuous_restrictionLaw f).tendsto μ |>.comp hlim
    have hd := he.dist hf
    have hz : Tendsto (fun k : ℕ => 1 / ((k : ℝ) + 1)) atTop (𝓝 0) := by
      exact tendsto_one_div_add_atTop_nhds_zero_nat
    have hzero : Tendsto (fun k =>
        dist (restrictionLaw e (seq (φ k))) (restrictionLaw f (seq (φ k)))) atTop (𝓝 0) :=
      squeeze_zero' (Eventually.of_forall (fun _ => dist_nonneg))
        (hφ.tendsto_atTop.eventually (hhom n e f)) (hz.comp hφ.tendsto_atTop)
    have hdz : dist (restrictionLaw e μ) (restrictionLaw f μ) = 0 :=
      tendsto_nhds_unique hd hzero
    exact dist_eq_zero.mp hdz
  let E : Set (ListPattern s d ℚ) := {C | ¬GoodPatternOn (C.restrict e₀) Finset.univ}
  have hzero : (μ : Measure (ListPattern s d ℚ)) E = 0 := by
    apply ae_iff.mp
    exact (invariant_pattern_globally_aligned _ hinv).mono (fun C hC =>
      hC.good_full_restrict C e₀)
  have hzero' : μ E = 0 := (μ.null_iff_toMeasure_null E).mpr hzero
  have hprob := ProbabilityMeasure.tendsto_measure_of_isClopen_of_tendsto hlim
    (isClopen_bad_restrict e₀)
  have hreal : Tendsto (fun k => ((seq (φ k)) E : ℝ)) atTop (𝓝 0) := by
    have hp : Tendsto (fun k => (seq (φ k)) E) atTop (𝓝 (μ E)) := hprob
    have hh := (NNReal.continuous_coe.tendsto (μ E)).comp hp
    simpa only [Function.comp_def, hzero', NNReal.coe_zero] using hh
  have hle : ξ ≤ 0 := ge_of_tendsto hreal (hφ.tendsto_atTop.eventually hbad)
  exact (not_le_of_gt hξ) hle

end LargeIndependentSets

end OAI
