import Mathlib

namespace OAI

namespace LargeIndependentSets
open Filter

abbrev ListIndex (s : ℕ) (X : Type*) :=
  {I : Finset X // I.Nonempty ∧ I.card ≤ s}

abbrev ListSlot (s d : ℕ) (X : Type*) := ListIndex s X × Fin d

abbrev EqualityData (s d : ℕ) (X : Type*) := ListSlot s d X → ListSlot s d X → Bool

def IsPattern {s d : ℕ} {X : Type*} [LinearOrder X]
    (C : EqualityData s d X) : Prop :=
  (∀ a b, C a b = true → C b a = true) ∧
  (∀ a b c, C a b = true → C b c = true → C a c = true) ∧
  (∀ a b, C a b = true → a.1 = b.1 → a.2 = b.2) ∧
  (∀ a b, (∀ x ∈ a.1.val, ∀ y ∈ b.1.val, x < y) → C a b = false)

abbrev ListPattern (s d : ℕ) (X : Type*) [LinearOrder X] :=
  {C : EqualityData s d X // IsPattern C}

lemma isClosed_isPattern (s d : ℕ) (X : Type*) [LinearOrder X] :
    IsClosed {C : EqualityData s d X | IsPattern C} := by
  classical
  have ev (a b : ListSlot s d X) : Continuous (fun C : EqualityData s d X => C a b) :=
    (continuous_apply b).comp (continuous_apply a)
  have cl (a b : ListSlot s d X) (v : Bool) :
      IsClosed {C : EqualityData s d X | C a b = v} :=
    isClosed_eq (ev a b) continuous_const
  have op (a b : ListSlot s d X) (v : Bool) :
      IsOpen {C : EqualityData s d X | C a b = v} :=
    (isOpen_discrete {v}).preimage (ev a b)
  have hsym : IsClosed {C : EqualityData s d X |
      ∀ a b, C a b = true → C b a = true} := by
    simp only [Set.ofPred_forall]
    apply isClosed_iInter; intro a
    apply isClosed_iInter; intro b
    convert (op a b true).isClosed_compl.union (cl b a true) using 1
    ext C; simp only [Set.mem_ofPred_eq, Set.mem_union, Set.mem_compl_iff]; tauto
  have htrans : IsClosed {C : EqualityData s d X |
      ∀ a b c, C a b = true → C b c = true → C a c = true} := by
    simp only [Set.ofPred_forall]
    apply isClosed_iInter; intro a
    apply isClosed_iInter; intro b
    apply isClosed_iInter; intro c
    convert (op a b true).isClosed_compl.union
      ((op b c true).isClosed_compl.union (cl a c true)) using 1
    ext C; simp only [Set.mem_ofPred_eq, Set.mem_union, Set.mem_compl_iff]; tauto
  have hinj : IsClosed {C : EqualityData s d X |
      ∀ a b, C a b = true → a.1 = b.1 → a.2 = b.2} := by
    simp only [Set.ofPred_forall]
    apply isClosed_iInter; intro a
    apply isClosed_iInter; intro b
    by_cases h : a.1 = b.1 → a.2 = b.2
    · have he : {C : EqualityData s d X | C a b = true → a.1 = b.1 → a.2 = b.2} = Set.univ := by
        ext C; simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true]; exact fun _ => h
      rw [he]; exact isClosed_univ
    · convert (op a b true).isClosed_compl using 1
      ext C; simp only [Set.mem_ofPred_eq, Set.mem_compl_iff]; tauto
  have hsep : IsClosed {C : EqualityData s d X |
      ∀ a b, (∀ x ∈ a.1.val, ∀ y ∈ b.1.val, x < y) → C a b = false} := by
    simp only [Set.ofPred_forall]
    apply isClosed_iInter; intro a
    apply isClosed_iInter; intro b
    apply isClosed_iInter; intro _
    exact cl a b false
  exact hsym.inter (htrans.inter (hinj.inter hsep))

instance (s d : ℕ) (X : Type*) [LinearOrder X] : CompactSpace (ListPattern s d X) :=
  isCompact_iff_compactSpace.mp (isClosed_isPattern s d X).isCompact

noncomputable instance (s d : ℕ) (X : Type*) [LinearOrder X] [Fintype X] :
    Fintype (ListPattern s d X) := Fintype.ofFinite _

instance (s d : ℕ) (X : Type*) [LinearOrder X] : Inhabited (ListPattern s d X) :=
  ⟨⟨fun _ _ => false, by simp [IsPattern]⟩⟩

def ListIndex.map {s : ℕ} {X Y : Type*} (e : X ↪ Y) (I : ListIndex s X) :
    ListIndex s Y :=
  ⟨I.val.map e, I.property.1.map, by simpa using I.property.2⟩

def ListSlot.map {s d : ℕ} {X Y : Type*} (e : X ↪ Y) (a : ListSlot s d X) :
    ListSlot s d Y := (ListIndex.map e a.1, a.2)

lemma ListIndex.map_injective {s : ℕ} {X Y : Type*} (e : X ↪ Y) :
    Function.Injective (ListIndex.map (s := s) e) := by
  intro I J h
  apply Subtype.ext
  exact Finset.map_injective e (congrArg Subtype.val h)

lemma ListSlot.map_injective {s d : ℕ} {X Y : Type*} (e : X ↪ Y) :
    Function.Injective (ListSlot.map (s := s) (d := d) e) := by
  intro a b h
  exact Prod.ext (ListIndex.map_injective e (congrArg Prod.fst h))
    (show a.2 = b.2 from congrArg (fun c : ListSlot s d Y => c.2) h)

def ListPattern.restrict {s d : ℕ} {X Y : Type*} [LinearOrder X] [LinearOrder Y]
    (e : X ↪o Y) (C : ListPattern s d Y) : ListPattern s d X :=
  ⟨fun a b => C.val (ListSlot.map e.toEmbedding a) (ListSlot.map e.toEmbedding b), by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro a b h; exact C.property.1 _ _ h
    · intro a b c hab hbc; exact C.property.2.1 _ _ _ hab hbc
    · intro a b h hab
      exact C.property.2.2.1 _ _ h (congrArg (ListIndex.map e.toEmbedding) hab)
    · intro a b hsep
      apply C.property.2.2.2
      intro x hx y hy
      obtain ⟨i, hi, rfl⟩ := Finset.mem_map.mp hx
      obtain ⟨j, hj, rfl⟩ := Finset.mem_map.mp hy
      exact e.strictMono (hsep i hi j hj)⟩

lemma ListPattern.continuous_restrict {s d : ℕ} {X Y : Type*}
    [LinearOrder X] [LinearOrder Y] (e : X ↪o Y) :
    Continuous (ListPattern.restrict (s := s) (d := d) e) := by
  apply Continuous.subtype_mk
  apply continuous_pi; intro a
  apply continuous_pi; intro b
  exact ((continuous_apply (ListSlot.map e.toEmbedding b)).comp
    (continuous_apply (ListSlot.map e.toEmbedding a) :
      Continuous (fun C : EqualityData s d Y => C (ListSlot.map e.toEmbedding a)))).comp
        continuous_subtype_val

lemma ListIndex.min_map {s : ℕ} {X Y : Type*} [LinearOrder X] [LinearOrder Y]
    (e : X ↪o Y) (I : ListIndex s X) :
    (ListIndex.map e.toEmbedding I).val.min' (ListIndex.map e.toEmbedding I).property.1 =
      e (I.val.min' I.property.1) := by
  apply le_antisymm
  · apply Finset.min'_le
    exact Finset.mem_map.mpr ⟨_, Finset.min'_mem _ _, rfl⟩
  · obtain ⟨x, hx, he⟩ := Finset.mem_map.mp
      (Finset.min'_mem (ListIndex.map e.toEmbedding I).val _)
    rw [← he]
    exact e.monotone (Finset.min'_le _ _ hx)

lemma ListPattern.occupied_of_eq {s d : ℕ} {X : Type*} [LinearOrder X]
    (C : ListPattern s d X) {a b : ListSlot s d X} (h : C.val a b = true) :
    C.val a a = true := C.property.2.1 _ _ _ h (C.property.1 _ _ h)

lemma ListPattern.min_le_max {s d : ℕ} {X : Type*} [LinearOrder X]
    (C : ListPattern s d X) {a b : ListSlot s d X} (h : C.val a b = true) :
    b.1.val.min' b.1.property.1 ≤ a.1.val.max' a.1.property.1 := by
  by_contra hn
  have hlt := lt_of_not_ge hn
  have hh := C.property.2.2.2 a b (by
    intro x hx y hy
    exact lt_of_le_of_lt (Finset.le_max' _ _ hx)
      (lt_of_lt_of_le hlt (Finset.min'_le _ _ hy)))
  exact Bool.false_ne_true (hh.symm.trans h)

noncomputable def patternCutValues {s d : ℕ} (C : ListPattern s d ℚ)
    (a : ListSlot s d ℚ) : Set ℝ :=
  insert ((a.1.val.min' a.1.property.1 : ℚ) : ℝ)
    {x | ∃ b : ListSlot s d ℚ, C.val a b = true ∧
      x = (b.1.val.min' b.1.property.1 : ℚ)}

lemma patternCutValues_nonempty {s d : ℕ} (C : ListPattern s d ℚ)
    (a : ListSlot s d ℚ) : (patternCutValues C a).Nonempty := ⟨_, Or.inl rfl⟩

lemma patternCutValues_bddAbove {s d : ℕ} (C : ListPattern s d ℚ)
    (a : ListSlot s d ℚ) : BddAbove (patternCutValues C a) := by
  refine ⟨(a.1.val.max' a.1.property.1 : ℚ), ?_⟩
  intro x hx
  rcases hx with rfl | ⟨b, hab, rfl⟩
  · exact_mod_cast Finset.min'_le _ _ (Finset.max'_mem _ _)
  · exact_mod_cast C.min_le_max hab

noncomputable def patternCut {s d : ℕ} (C : ListPattern s d ℚ)
    (a : ListSlot s d ℚ) : ℝ := sSup (patternCutValues C a)

lemma patternCut_le_iff {s d : ℕ} (C : ListPattern s d ℚ)
    (a : ListSlot s d ℚ) (q : ℝ) :
    patternCut C a ≤ q ↔
      (a.1.val.min' a.1.property.1 : ℚ) ≤ q ∧
      ∀ b, C.val a b = true → (b.1.val.min' b.1.property.1 : ℚ) ≤ q := by
  rw [patternCut, csSup_le_iff (patternCutValues_bddAbove C a)
    (patternCutValues_nonempty C a)]
  constructor
  · intro h
    exact ⟨h _ (Or.inl rfl), fun b hb => h _ (Or.inr ⟨b, hb, rfl⟩)⟩
  · rintro ⟨ha, hb⟩ x (rfl | ⟨b, hab, rfl⟩)
    · exact ha
    · exact hb b hab

lemma patternCut_hull {s d : ℕ} (C : ListPattern s d ℚ)
    (a : ListSlot s d ℚ) :
    (a.1.val.min' a.1.property.1 : ℚ) ≤ patternCut C a ∧
      patternCut C a ≤ (a.1.val.max' a.1.property.1 : ℚ) := by
  constructor
  · exact le_csSup (patternCutValues_bddAbove C a) (Or.inl rfl)
  · apply (patternCut_le_iff C a _).mpr
    constructor
    · exact_mod_cast Finset.min'_le _ _ (Finset.max'_mem _ _)
    · intro b hb; exact_mod_cast C.min_le_max hb

lemma patternCut_eq_of_eq {s d : ℕ} (C : ListPattern s d ℚ)
    (a b : ListSlot s d ℚ) (hab : C.val a b = true) :
    patternCut C a = patternCut C b := by
  have hv (a b : ListSlot s d ℚ) (hab : C.val a b = true) :
      patternCutValues C a ⊆ patternCutValues C b := by
    intro x hx
    rcases hx with rfl | ⟨c, hc, rfl⟩
    · exact Or.inr ⟨a, C.property.1 a b hab, rfl⟩
    · exact Or.inr ⟨c, C.property.2.1 b a c (C.property.1 a b hab) hc, rfl⟩
  exact congrArg sSup (Set.Subset.antisymm (hv a b hab) (hv b a (C.property.1 a b hab)))

lemma patternEval_continuous {s d : ℕ} {X : Type*} [LinearOrder X]
    (a b : ListSlot s d X) : Continuous (fun C : ListPattern s d X => C.val a b) :=
  ((continuous_apply b).comp (continuous_apply a :
    Continuous (fun C : EqualityData s d X => C a))).comp continuous_subtype_val

lemma patternCut_measurable {s d : ℕ} (a : ListSlot s d ℚ) :
    Measurable (fun C : ListPattern s d ℚ => patternCut C a) := by
  classical
  apply measurable_of_Iic
  intro q
  have he : (fun C : ListPattern s d ℚ => patternCut C a) ⁻¹' Set.Iic q =
      {C : ListPattern s d ℚ | (a.1.val.min' a.1.property.1 : ℚ) ≤ q} ∩
      ⋂ b : ListSlot s d ℚ, {C : ListPattern s d ℚ |
        C.val a b = true → (b.1.val.min' b.1.property.1 : ℚ) ≤ q} := by
    ext C
    simp only [Set.mem_preimage, Set.mem_Iic, Set.mem_inter_iff,
      Set.mem_ofPred_eq, Set.mem_iInter, patternCut_le_iff]
  rw [he]
  apply MeasurableSet.inter (by
    by_cases h : ((a.1.val.min' a.1.property.1 : ℚ) : ℝ) ≤ q <;> simp [h])
  apply MeasurableSet.iInter; intro b
  by_cases h : (b.1.val.min' b.1.property.1 : ℚ) ≤ q
  · simp only [h, implies_true, Set.ofPred_true]; exact MeasurableSet.univ
  · have he : {C : ListPattern s d ℚ |
          C.val a b = true → (b.1.val.min' b.1.property.1 : ℚ) ≤ q} =
        {C : ListPattern s d ℚ | C.val a b = true}ᶜ := by
      ext C; simp only [Set.mem_ofPred_eq, Set.mem_compl_iff]; tauto
    rw [he]
    exact ((isClosed_eq (patternEval_continuous a b) continuous_const).measurableSet).compl

noncomputable def ListIndex.mapEquiv {s : ℕ} {X Y : Type*}
    [LinearOrder X] [LinearOrder Y] (e : X ≃o Y) : ListIndex s X ≃ ListIndex s Y where
  toFun := ListIndex.map e.toEmbedding
  invFun := ListIndex.map e.symm.toEmbedding
  left_inv I := by
    apply Subtype.ext
    ext x
    simp [ListIndex.map]
  right_inv I := by
    apply Subtype.ext
    ext x
    simp [ListIndex.map]

noncomputable def ListSlot.mapEquiv {s d : ℕ} {X Y : Type*}
    [LinearOrder X] [LinearOrder Y] (e : X ≃o Y) : ListSlot s d X ≃ ListSlot s d Y :=
  (ListIndex.mapEquiv e).prodCongr (Equiv.refl (Fin d))

lemma ListSlot.mapEquiv_apply {s d : ℕ} {X Y : Type*}
    [LinearOrder X] [LinearOrder Y] (e : X ≃o Y) (a : ListSlot s d X) :
    ListSlot.mapEquiv e a = ListSlot.map e.toEmbedding a := rfl

lemma patternCut_rat_iff {s d : ℕ} (C : ListPattern s d ℚ)
    (a : ListSlot s d ℚ) (q : ℚ) :
    patternCut C a ≤ (q : ℝ) ↔
      a.1.val.min' a.1.property.1 ≤ q ∧
      ∀ b, C.val a b = true → b.1.val.min' b.1.property.1 ≤ q := by
  simpa only [Rat.cast_le] using patternCut_le_iff C a (q : ℝ)

lemma patternCut_restrict_CDF {s d : ℕ} (C : ListPattern s d ℚ)
    (e : ℚ ≃o ℚ) (a : ListSlot s d ℚ) (q : ℚ) :
    patternCut (ListPattern.restrict e.toOrderEmbedding C) a ≤ (q : ℝ) ↔
      patternCut C (ListSlot.map e.toEmbedding a) ≤ (e q : ℝ) := by
  have hmin (I : ListIndex s ℚ) :
      (ListIndex.map e.toEmbedding I).val.min' _ = e (I.val.min' I.property.1) :=
    ListIndex.min_map e.toOrderEmbedding I
  rw [patternCut_rat_iff, patternCut_rat_iff]
  change (_ ≤ q ∧ ∀ b, C.val (ListSlot.map e.toEmbedding a)
      (ListSlot.map e.toEmbedding b) = true → _ ≤ q) ↔ _
  rw [show (ListSlot.map e.toEmbedding a).1 = ListIndex.map e.toEmbedding a.1 from rfl,
    hmin, e.le_iff_le]
  constructor
  · rintro ⟨ha, h⟩
    refine ⟨ha, ?_⟩
    intro b hb
    obtain ⟨b', rfl⟩ := (ListSlot.mapEquiv (s := s) (d := d) e).surjective b
    change (ListIndex.map e.toEmbedding b'.1).val.min' _ ≤ e q
    rw [hmin, e.le_iff_le]
    exact h b' hb
  · rintro ⟨ha, h⟩
    refine ⟨ha, ?_⟩
    intro b hb
    have hh := h (ListSlot.map e.toEmbedding b) hb
    change (ListIndex.map e.toEmbedding b.1).val.min' _ ≤ e q at hh
    rwa [hmin, e.le_iff_le] at hh

lemma ListSlot.map_eq_self {s d : ℕ} (e : ℚ ≃o ℚ) (a : ListSlot s d ℚ)
    (he : ∀ i ∈ a.1.val, e i = i) : ListSlot.map e.toEmbedding a = a := by
  apply Prod.ext
  · apply Subtype.ext
    ext x
    constructor
    · intro hx
      obtain ⟨y, hy, hxy⟩ := Finset.mem_map.mp hx
      change e y = x at hxy
      rw [he y hy] at hxy
      exact hxy ▸ hy
    · intro hx
      exact Finset.mem_map.mpr ⟨x, hx, he x hx⟩
  · rfl

open MeasureTheory Set in

theorem invariant_cut_support_open (I : Finset ℚ) (ν : Measure ℝ) [IsFiniteMeasure ν]
    (hCDF : ∀ a b : ℚ, a < b → a ∉ I → b ∉ I →
      (∀ i ∈ I, i < a ↔ i < b) → ν (Iic (a : ℝ)) = ν (Iic (b : ℝ))) :
    ν (((↑I : Set ℚ).image ((↑) : ℚ → ℝ))ᶜ) = 0 := by
  classical
  let Intervals := {p : ℚ × ℚ // p.1 < p.2 ∧ p.1 ∉ I ∧ p.2 ∉ I ∧
    ∀ i ∈ I, i < p.1 ↔ i < p.2}
  have hnull (p : Intervals) : ν (Ioc (p.val.1 : ℝ) (p.val.2 : ℝ)) = 0 := by
    have hp : (p.val.1 : ℝ) ≤ (p.val.2 : ℝ) := by exact_mod_cast p.property.1.le
    rw [← Iic_sdiff_Iic, measure_sdiff (Iic_subset_Iic.mpr hp)
      measurableSet_Iic.nullMeasurableSet (measure_ne_top ν _)]
    rw [hCDF _ _ p.property.1 p.property.2.1 p.property.2.2.1 p.property.2.2.2, tsub_self]
  apply measure_mono_null (t := ⋃ p : Intervals, Ioc (p.val.1 : ℝ) (p.val.2 : ℝ))
  · intro x hx
    have hclosed : IsClosed ((↑I : Set ℚ).image ((↑) : ℚ → ℝ)) :=
      (I.finite_toSet.image _).isClosed
    obtain ⟨u, v, huxv, huv⟩ := mem_nhds_iff_exists_Ioo_subset.mp
      (hclosed.isOpen_compl.mem_nhds hx)
    obtain ⟨a, hua, hax⟩ := exists_rat_btwn huxv.1
    obtain ⟨b, hxb, hbv⟩ := exists_rat_btwn huxv.2
    have hab : a < b := by exact_mod_cast hax.trans hxb
    have ha : a ∉ I := by
      intro ha
      exact (huv ⟨hua, hax.trans huxv.2⟩) ⟨a, ha, rfl⟩
    have hb : b ∉ I := by
      intro hb
      exact (huv ⟨huxv.1.trans hxb, hbv⟩) ⟨b, hb, rfl⟩
    have hg : ∀ i ∈ I, i < a ↔ i < b := by
      intro i hi
      constructor
      · intro hia; exact hia.trans hab
      · intro hib
        by_contra hia
        have hai := le_of_not_gt hia
        have hai' : (a : ℝ) ≤ (i : ℝ) := by exact_mod_cast hai
        have hib' : (i : ℝ) < (b : ℝ) := by exact_mod_cast hib
        exact (huv ⟨hua.trans_le hai', hib'.trans hbv⟩) ⟨i, hi, rfl⟩
    exact mem_iUnion.mpr ⟨⟨(a, b), hab, ha, hb, hg⟩, hax, hxb.le⟩
  · exact measure_iUnion_null hnull

end LargeIndependentSets

end OAI
