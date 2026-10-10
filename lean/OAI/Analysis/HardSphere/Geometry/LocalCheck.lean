import Mathlib

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
open MeasureTheory Function Set Filter
open scoped ENNReal BigOperators
namespace HardSphere.Comparison

variable {ι : Type*} [DecidableEq ι] {X : ι → Type*}
  [∀ i, MeasurableSpace (X i)]

structure LocalCheck (X : ι → Type*) [∀ i, MeasurableSpace (X i)] where
  support : Finset ι
  nonempty : support.Nonempty
  arity : support.card ≤ 2
  pass : (∀ i, X i) → Prop
  measurable_pass : MeasurableSet {x | pass x}
  depends : ∀ x y, (∀ i ∈ support, x i = y i) → (pass x ↔ pass y)

variable {C : Type*} [Fintype C] (checks : C → LocalCheck X)

def retainedEvent (s : Finset ι) : Set (∀ i, X i) :=
  {x | ∀ c, (checks c).support ⊆ s → (checks c).pass x}

def insertionEvent (s : Finset ι) (i : ι) : Set (∀ i, X i) :=
  {x | ∀ c, (checks c).support ⊆ insert i s →
    ¬ (checks c).support ⊆ s → (checks c).pass x}

lemma measurableSet_retainedEvent (s : Finset ι) : MeasurableSet (retainedEvent checks s) := by
  classical
  have heq : retainedEvent checks s =
      ⋂ c, if (checks c).support ⊆ s then {x | (checks c).pass x} else Set.univ := by
    ext x
    simp [retainedEvent]
  rw [heq]
  apply MeasurableSet.iInter
  intro c
  split_ifs
  · exact (checks c).measurable_pass
  · exact MeasurableSet.univ

lemma measurableSet_insertionEvent (s : Finset ι) (i : ι) :
    MeasurableSet (insertionEvent checks s i) := by
  classical
  have heq : insertionEvent checks s i =
      ⋂ c, if (checks c).support ⊆ insert i s ∧ ¬ (checks c).support ⊆ s then
        {x | (checks c).pass x} else Set.univ := by
    ext x
    simp [insertionEvent, and_imp]
  rw [heq]
  apply MeasurableSet.iInter
  intro c
  split_ifs
  · exact (checks c).measurable_pass
  · exact MeasurableSet.univ

omit [Fintype C] in
lemma retainedEvent_insert (s : Finset ι) (i : ι) :
    retainedEvent checks (insert i s) =
      retainedEvent checks s ∩ insertionEvent checks s i := by
  classical
  ext x
  constructor
  · intro h
    exact ⟨fun c hc ↦ h c (hc.trans (Finset.subset_insert _ _)), fun c hc _ ↦ h c hc⟩
  · rintro ⟨hs, hi⟩ c hc
    by_cases hold : (checks c).support ⊆ s
    · exact hs c hold
    · exact hi c hc hold

omit [Fintype C] in
lemma retainedEvent_update {s : Finset ι} {i : ι} (hi : i ∉ s)
    (x : ∀ j, X j) (y : X i) :
    Function.update x i y ∈ retainedEvent checks s ↔ x ∈ retainedEvent checks s := by
  apply forall_congr'
  intro c
  apply imp_congr_right
  intro hc
  apply (checks c).depends
  intro j hj
  exact Function.update_of_ne (ne_of_mem_of_not_mem (hc hj) hi) y x

def checkWeight (s : Finset ι) : (∀ i, X i) → ℝ≥0∞ :=
  (retainedEvent checks s).indicator (fun _ ↦ 1)

lemma measurable_checkWeight (s : Finset ι) : Measurable (checkWeight checks s) :=
  measurable_const.indicator (measurableSet_retainedEvent checks s)

omit [DecidableEq ι] [Fintype C] in
lemma checkWeight_le_one (s : Finset ι) (x : ∀ i, X i) : checkWeight checks s x ≤ 1 := by
  classical
  simp only [checkWeight, Set.indicator_apply]
  split_ifs <;> simp

def UniformInsertion (μ : ∀ i, Measure (X i)) (a : ℝ≥0∞) : Prop :=
  ∀ (s : Finset ι) (i : ι), i ∉ s → ∀ x : ∀ j, X j,
    a ≤ ∫⁻ y, (insertionEvent checks s i).indicator (fun _ ↦ (1 : ℝ≥0∞))
      (Function.update x i y) ∂μ i

omit [Fintype C] in
lemma insertion_integral_lower {μ : ∀ i, Measure (X i)} {a : ℝ≥0∞}
    (hcompat : UniformInsertion checks μ a) {s : Finset ι} {i : ι} (hi : i ∉ s)
    (x : ∀ i, X i) :
    a * checkWeight checks s x ≤
      ∫⁻ y, checkWeight checks (insert i s) (Function.update x i y) ∂μ i := by
  classical
  by_cases hx : x ∈ retainedEvent checks s
  · have heq : (fun y ↦ checkWeight checks (insert i s) (Function.update x i y)) =
        fun y ↦ (insertionEvent checks s i).indicator (fun _ ↦ (1 : ℝ≥0∞))
          (Function.update x i y) := by
      funext y
      have hu := (retainedEvent_update checks hi x y).2 hx
      simp [checkWeight, retainedEvent_insert, Set.indicator_apply, hu]
    rw [heq]
    simpa [checkWeight, hx] using hcompat s i hi x
  · simp [checkWeight, hx]

def checkNormalizer (μ : ∀ i, Measure (X i)) (s : Finset ι)
    (x : ∀ i, X i) : ℝ≥0∞ := lmarginal μ s (checkWeight checks s) x

lemma checkNormalizer_insert_lower {μ : ∀ i, Measure (X i)} [∀ i, SigmaFinite (μ i)]
    {a : ℝ≥0∞} (hcompat : UniformInsertion checks μ a)
    {s : Finset ι} {i : ι} (hi : i ∉ s) (x : ∀ i, X i) :
    a * checkNormalizer checks μ s x ≤ checkNormalizer checks μ (insert i s) x := by
  rw [checkNormalizer, checkNormalizer,
    lmarginal_insert' _ (measurable_checkWeight checks _) hi]
  calc
    a * lmarginal μ s (checkWeight checks s) x =
        lmarginal μ s (fun x ↦ a * checkWeight checks s x) x := by
      dsimp [lmarginal]
      exact (lintegral_const_mul a ((measurable_checkWeight checks s).comp
        (measurable_updateFinset (x := x) (s := s)))).symm
    _ ≤ _ := lmarginal_mono (insertion_integral_lower checks hcompat hi) x

omit [DecidableEq ι] [Fintype C] in
lemma checkWeight_depends (s : Finset ι) {x y : ∀ i, X i}
    (hxy : ∀ i ∈ s, x i = y i) : checkWeight checks s x = checkWeight checks s y := by
  classical
  have h : x ∈ retainedEvent checks s ↔ y ∈ retainedEvent checks s := by
    apply forall_congr'
    intro c
    apply imp_congr_right
    intro hc
    exact (checks c).depends x y fun i hi ↦ hxy i (hc hi)
  simp only [checkWeight, Set.indicator_apply, h]

omit [Fintype C] in
lemma checkNormalizer_const {μ : ∀ i, Measure (X i)} (s : Finset ι)
    (x y : ∀ i, X i) : checkNormalizer checks μ s x = checkNormalizer checks μ s y := by
  apply lintegral_congr
  intro z
  apply checkWeight_depends
  intro i hi
  simp [Function.updateFinset, hi]

omit [Fintype C] in
lemma checkNormalizer_empty {μ : ∀ i, Measure (X i)} (x : ∀ i, X i) :
    checkNormalizer checks μ ∅ x = 1 := by
  have h : x ∈ retainedEvent checks ∅ := by
    intro c hc
    exact False.elim ((checks c).nonempty.ne_empty (Finset.subset_empty.mp hc))
  simp [checkNormalizer, checkWeight, h]

omit [Fintype C] in
lemma checkNormalizer_le_one {μ : ∀ i, Measure (X i)} [∀ i, IsProbabilityMeasure (μ i)]
    (s : Finset ι) (x : ∀ i, X i) : checkNormalizer checks μ s x ≤ 1 := by
  calc
    checkNormalizer checks μ s x ≤ ∫⁻ _, (1 : ℝ≥0∞) ∂Measure.pi (fun i : s ↦ μ i) :=
      lintegral_mono fun _ ↦ checkWeight_le_one checks _ _
    _ = 1 := by simp

lemma checkNormalizer_union_lower {μ : ∀ i, Measure (X i)} [∀ i, SigmaFinite (μ i)]
    {a : ℝ≥0∞} (hcompat : UniformInsertion checks μ a)
    (s t : Finset ι) (hst : Disjoint s t) (x : ∀ i, X i) :
    a ^ t.card * checkNormalizer checks μ s x ≤ checkNormalizer checks μ (s ∪ t) x := by
  induction t using Finset.induction_on with
  | empty => simp
  | @insert i t hit ih =>
    have his : i ∉ s := (Finset.disjoint_insert_right.mp hst).1
    have hst' : Disjoint s t := (Finset.disjoint_insert_right.mp hst).2
    have hiu : i ∉ s ∪ t := by simp [his, hit]
    calc
      a ^ (insert i t).card * checkNormalizer checks μ s x =
          a * (a ^ t.card * checkNormalizer checks μ s x) := by
        rw [Finset.card_insert_of_notMem hit, pow_succ]
        ac_rfl
      _ ≤ a * checkNormalizer checks μ (s ∪ t) x := mul_le_mul_right (ih hst') a
      _ ≤ checkNormalizer checks μ (insert i (s ∪ t)) x :=
        checkNormalizer_insert_lower checks hcompat hiu x
      _ = _ := by rw [Finset.union_insert]

lemma checkNormalizer_pos {μ : ∀ i, Measure (X i)} [∀ i, SigmaFinite (μ i)]
    {a : ℝ≥0∞} (ha : 0 < a) (hcompat : UniformInsertion checks μ a)
    (s : Finset ι) (x : ∀ i, X i) : 0 < checkNormalizer checks μ s x := by
  have h := checkNormalizer_union_lower checks hcompat ∅ s (Finset.disjoint_empty_left s) x
  simp only [checkNormalizer_empty, mul_one, Finset.empty_union] at h
  exact lt_of_lt_of_le (by positivity) h

omit [DecidableEq ι] [Fintype C] in
lemma checkWeight_antitone {s t : Finset ι} (hst : s ⊆ t) :
    checkWeight checks t ≤ checkWeight checks s := by
  classical
  intro x
  by_cases ht : x ∈ retainedEvent checks t
  · have hs : x ∈ retainedEvent checks s := fun c hc ↦ ht c (hc.trans hst)
    simp [checkWeight, ht, hs]
  · simp [checkWeight, ht]

lemma checkNormalizer_antitone {μ : ∀ i, Measure (X i)} [∀ i, IsProbabilityMeasure (μ i)]
    {s t : Finset ι} (hst : s ⊆ t) (x : ∀ i, X i) :
    checkNormalizer checks μ t x ≤ checkNormalizer checks μ s x := by
  calc
    checkNormalizer checks μ t x ≤ lmarginal μ t (checkWeight checks s) x :=
      lmarginal_mono (checkWeight_antitone checks hst) x
    _ = checkNormalizer checks μ s x := by
      rw [← Finset.union_sdiff_of_subset hst,
        lmarginal_union' μ _ (measurable_checkWeight checks s) Finset.disjoint_sdiff]
      change (∫⁻ y, checkNormalizer checks μ s (Function.updateFinset x (t \ s) y)
        ∂Measure.pi (fun i : ↥(t \ s) ↦ μ i)) = checkNormalizer checks μ s x
      simp_rw [checkNormalizer_const checks s _ x]
      simp

def SeparatedChecks (s t : Finset ι) : Prop :=
  ∀ c, (checks c).support ⊆ s ∪ t →
    (checks c).support ⊆ s ∨ (checks c).support ⊆ t

omit [Fintype C] in
lemma checkWeight_union {s t : Finset ι} (hsep : SeparatedChecks checks s t)
    (x : ∀ i, X i) :
    checkWeight checks (s ∪ t) x = checkWeight checks s x * checkWeight checks t x := by
  classical
  have hevent : x ∈ retainedEvent checks (s ∪ t) ↔
      x ∈ retainedEvent checks s ∧ x ∈ retainedEvent checks t := by
    constructor
    · intro h
      exact ⟨fun c hc ↦ h c (hc.trans Finset.subset_union_left),
        fun c hc ↦ h c (hc.trans Finset.subset_union_right)⟩
    · rintro ⟨hs, ht⟩ c hc
      exact (hsep c hc).elim (hs c) (ht c)
  simp only [checkWeight, Set.indicator_apply, hevent]
  split_ifs <;> simp_all

lemma checkNormalizer_union_eq_mul {μ : ∀ i, Measure (X i)} [∀ i, SigmaFinite (μ i)]
    {s t : Finset ι} (hst : Disjoint s t) (hsep : SeparatedChecks checks s t)
    (x : ∀ i, X i) :
    checkNormalizer checks μ (s ∪ t) x =
      checkNormalizer checks μ s x * checkNormalizer checks μ t x := by
  have hin : ∀ y, lmarginal μ t
      (fun y ↦ checkWeight checks s y * checkWeight checks t y) y =
      checkWeight checks s y * checkNormalizer checks μ t y := by
    intro y
    simp only [lmarginal, checkNormalizer]
    have hu : ∀ z : ∀ i : t, X i,
        checkWeight checks s (Function.updateFinset y t z) = checkWeight checks s y := by
      intro z
      apply checkWeight_depends
      intro i hi
      have hit : i ∉ t := Finset.disjoint_left.mp hst hi
      simp [Function.updateFinset, hit]
    simp_rw [hu]
    exact lintegral_const_mul _ ((measurable_checkWeight checks t).comp
      (measurable_updateFinset (x := y) (s := t)))
  rw [checkNormalizer, show checkWeight checks (s ∪ t) =
    (fun y ↦ checkWeight checks s y * checkWeight checks t y) from
      funext (checkWeight_union checks hsep)]
  rw [lmarginal_union μ (fun y ↦ checkWeight checks s y * checkWeight checks t y)
    ((measurable_checkWeight checks s).mul (measurable_checkWeight checks t)) hst]
  simp_rw [show lmarginal μ t (fun y ↦ checkWeight checks s y * checkWeight checks t y) =
    (fun y ↦ checkWeight checks s y * checkNormalizer checks μ t y) from funext hin]
  simp only [lmarginal]
  simp_rw [checkNormalizer_const checks t _ x]
  exact lintegral_mul_const _ ((measurable_checkWeight checks s).comp
    (measurable_updateFinset (x := x) (s := s)))

lemma checkNormalizer_far_lower {μ : ∀ i, Measure (X i)} [∀ i, SigmaFinite (μ i)]
    {a : ℝ≥0∞} (hcompat : UniformInsertion checks μ a)
    {s t u : Finset ι} (hst : Disjoint s t) (hu : Disjoint (s ∪ t) u)
    (hsep : SeparatedChecks checks s t) (x : ∀ i, X i) :
    a ^ u.card * (checkNormalizer checks μ s x * checkNormalizer checks μ t x) ≤
      checkNormalizer checks μ (s ∪ t ∪ u) x := by
  rw [← checkNormalizer_union_eq_mul checks hst hsep x]
  exact checkNormalizer_union_lower checks hcompat _ _ hu x

omit [Fintype C] in
lemma lmarginal_eq_const_of_depends {μ : ∀ i, Measure (X i)}
    {s : Finset ι} {f : (∀ i, X i) → ℝ≥0∞}
    (hf : DependsOn f (s : Set ι)) (x y : ∀ i, X i) :
    lmarginal μ s f x = lmarginal μ s f y := by
  apply lintegral_congr
  intro z
  apply hf
  intro i hi
  change i ∈ s at hi
  simp [Function.updateFinset, hi]

omit [Fintype C] in
lemma lmarginal_of_disjoint_depends {μ : ∀ i, Measure (X i)}
    [∀ i, IsProbabilityMeasure (μ i)]
    {s t : Finset ι} {f : (∀ i, X i) → ℝ≥0∞}
    (hf : DependsOn f (s : Set ι)) (hst : Disjoint s t) (x : ∀ i, X i) :
    lmarginal μ t f x = f x := by
  have hu : ∀ z : ∀ i : t, X i, f (Function.updateFinset x t z) = f x := by
    intro z
    apply hf
    intro i hi
    have hit : i ∉ t := Finset.disjoint_left.mp hst hi
    simp [Function.updateFinset, hit]
  simp only [lmarginal]
  simp_rw [hu]
  simp

omit [Fintype C] in
lemma lmarginal_mul_disjoint {μ : ∀ i, Measure (X i)} [∀ i, SigmaFinite (μ i)]
    {s t : Finset ι} (hst : Disjoint s t) {f g : (∀ i, X i) → ℝ≥0∞}
    (hf : Measurable f) (hg : Measurable g)
    (hfs : DependsOn f (s : Set ι)) (hgt : DependsOn g (t : Set ι))
    (x : ∀ i, X i) :
    lmarginal μ (s ∪ t) (fun y ↦ f y * g y) x =
      lmarginal μ s f x * lmarginal μ t g x := by
  have hin : ∀ y, lmarginal μ t (fun y ↦ f y * g y) y =
      f y * lmarginal μ t g y := by
    intro y
    simp only [lmarginal]
    have hu : ∀ z : ∀ i : t, X i, f (Function.updateFinset y t z) = f y := by
      intro z
      apply hfs
      intro i hi
      have hit : i ∉ t := Finset.disjoint_left.mp hst hi
      simp [Function.updateFinset, hit]
    simp_rw [hu]
    exact lintegral_const_mul _ (hg.comp (measurable_updateFinset (x := y) (s := t)))
  rw [lmarginal_union μ (fun y ↦ f y * g y) (hf.mul hg) hst]
  simp_rw [show lmarginal μ t (fun y ↦ f y * g y) =
    (fun y ↦ f y * lmarginal μ t g y) from funext hin]
  change (∫⁻ y, f (Function.updateFinset x s y) *
    lmarginal μ t g (Function.updateFinset x s y)
    ∂Measure.pi (fun i : s ↦ μ i)) = _
  simp_rw [lmarginal_eq_const_of_depends hgt _ x]
  exact lintegral_mul_const _ (hf.comp (measurable_updateFinset (x := x) (s := s)))

omit [Fintype C] in
lemma lmarginal_prod_coordinates {μ : ∀ i, Measure (X i)} [∀ i, SigmaFinite (μ i)]
    (g : ∀ i, X i → ℝ≥0∞) (hg : ∀ i, Measurable (g i))
    (s : Finset ι) (x : ∀ i, X i) :
    lmarginal μ s (fun y ↦ ∏ i ∈ s, g i (y i)) x =
      ∏ i ∈ s, ∫⁻ y, g i y ∂μ i := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    have hm (s : Finset ι) : Measurable (fun y : ∀ i, X i ↦ ∏ i ∈ s, g i (y i)) :=
      Finset.measurable_prod s fun i _ ↦ (hg i).comp (measurable_pi_apply i)
    have hs : DependsOn (fun y : ∀ i, X i ↦ ∏ i ∈ s, g i (y i)) (s : Set ι) := by
      intro y z hyz
      exact Finset.prod_congr rfl fun i hi ↦ congrArg (g i) (hyz i hi)
    have hu : (insert i s : Finset ι) = {i} ∪ s := by simp
    simp only [Finset.prod_insert hi]
    rw [hu, lmarginal_mul_disjoint (μ := μ)
      (f := fun y ↦ g i (y i)) (g := fun y ↦ ∏ i ∈ s, g i (y i))
      (Finset.disjoint_singleton_left.mpr hi)
      ((hg i).comp (measurable_pi_apply i)) (hm s)
      (by intro y z hyz; exact congrArg (g i) (hyz i (by simp))) hs x]
    rw [ih, lmarginal_singleton]
    simp

lemma checkNormalizer_delete_le {μ : ∀ i, Measure (X i)} [∀ i, SigmaFinite (μ i)]
    {s t : Finset ι} (hst : Disjoint s t) (x : ∀ i, X i) :
    checkNormalizer checks μ (s ∪ t) x ≤
      checkNormalizer checks μ s x * ∏ i ∈ t, μ i Set.univ := by
  calc
    checkNormalizer checks μ (s ∪ t) x ≤ lmarginal μ (s ∪ t) (checkWeight checks s) x :=
      lmarginal_mono (checkWeight_antitone checks Finset.subset_union_left) x
    _ = checkNormalizer checks μ s x * ∏ i ∈ t, μ i Set.univ := by
      rw [lmarginal_union' μ _ (measurable_checkWeight checks s) hst]
      change (∫⁻ y, checkNormalizer checks μ s (Function.updateFinset x t y)
        ∂Measure.pi (fun i : t ↦ μ i)) = _
      simp_rw [checkNormalizer_const checks s _ x]
      rw [lintegral_const]
      rw [Measure.pi_univ]
      exact congrArg (checkNormalizer checks μ s x * ·)
        (Finset.prod_coe_sort t (fun i ↦ μ i Set.univ))

end HardSphere.Comparison

end

end OAI
