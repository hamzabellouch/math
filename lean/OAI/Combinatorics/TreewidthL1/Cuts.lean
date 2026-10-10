import OAI.Combinatorics.TreewidthL1.WeightedPaths

namespace OAI

universe treewidthLevel1

namespace BoundedTreewidthL1
open MeasureTheory Set
open scoped ENNReal

variable {V : Type*} [Fintype V]

noncomputable def thresholdLabels (F : V → ℝ) (t : ℝ) : V → Bool :=
  fun v => decide (t < F v)

noncomputable def sweep (M : ℝ) (F : V → ℝ) : Measure (V → Bool) :=
  (volume.restrict (Icc (-M) M)).map (thresholdLabels F)

def complementCut (ω : V → Bool) : V → Bool := fun v => !(ω v)

noncomputable def symmetrizeCut (μ : Measure (V → Bool)) : Measure (V → Bool) :=
  (1 / 2 : ℝ≥0∞) • (μ + μ.map complementCut)

def cutEvent (P : Finset V) (z : V) (b : P → Bool) (q : Bool) : Set (V → Bool) :=
  {ω | (∀ s : P, ω s = b s) ∧ ω z = q}

noncomputable def cutUncertainty (μ : Measure (V → Bool)) (P : Finset V) (z : V) : ℝ := by
  classical
  exact ∑ b : P → Bool, min (μ.real (cutEvent P z b false)) (μ.real (cutEvent P z b true))

end BoundedTreewidthL1

namespace BoundedTreewidthL1
open MeasureTheory Set
open scoped ENNReal
variable {V : Type*} [Fintype V]

lemma measurable_thresholdLabels
    {V : Type treewidthLevel1} [Fintype V]
    (F : V → ℝ) : Measurable (thresholdLabels F) := by
  apply Measurable.of_eval
  intro v
  have h : Measurable (fun t : ℝ => if t < F v then true else false) :=
    Measurable.ite (measurableSet_lt measurable_id measurable_const)
      measurable_const measurable_const
  convert h using 1
  ext t
  simp [thresholdLabels]

instance sweep_finite (M : ℝ) (F : V → ℝ) : IsFiniteMeasure (sweep M F) := by
  unfold sweep
  infer_instance

lemma cutEvent_measurable (P : Finset V) (z : V) (b : P → Bool) (q : Bool) :
    MeasurableSet (cutEvent P z b q) := (Set.toFinite _).measurableSet

lemma measurable_complementCut : Measurable (complementCut (V := V)) :=
  measurable_of_finite _

instance symmetrizeCut_finite (μ : Measure (V → Bool)) [IsFiniteMeasure μ] :
    IsFiniteMeasure (symmetrizeCut μ) := by
  constructor
  change (1 / 2 : ℝ≥0∞) * (μ + μ.map complementCut) Set.univ < ⊤
  finiteness

lemma complementCut_involutive
    {V : Type treewidthLevel1} [Fintype V] : Function.Involutive (complementCut (V := V)) := by
  intro ω
  funext v
  simp [complementCut]

def complementEquiv (V : Type*) : (V → Bool) ≃ (V → Bool) where
  toFun := complementCut
  invFun := complementCut
  left_inv := by intro ω; funext v; simp [complementCut]
  right_inv := by intro ω; funext v; simp [complementCut]

lemma complement_preimage_event
    {V : Type treewidthLevel1} [Fintype V]
    (P : Finset V) (z : V) (b : P → Bool) (q : Bool) :
    complementCut ⁻¹' cutEvent P z b q =
      cutEvent P z (complementCut b) (!q) := by
  ext ω
  simp only [Set.mem_preimage, cutEvent, Set.mem_ofPred_eq, complementCut]
  constructor
  · rintro ⟨h, hz⟩
    constructor
    · intro s
      have := congrArg Bool.not (h s)
      simpa using this
    · have := congrArg Bool.not hz
      simpa using this
  · rintro ⟨h, hz⟩
    constructor
    · intro s
      have := congrArg Bool.not (h s)
      simpa using this
    · have := congrArg Bool.not hz
      simpa using this

lemma uncertainty_nonneg
    {V : Type treewidthLevel1} [Fintype V]
    (μ : Measure (V → Bool)) (P : Finset V) (z : V) :
    0 ≤ cutUncertainty μ P z :=
  Finset.sum_nonneg (fun _ _ => le_min measureReal_nonneg measureReal_nonneg)

lemma uncertainty_add
    {V : Type treewidthLevel1} [Fintype V]
    (μ ν : Measure (V → Bool)) [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] (P : Finset V) (z : V) :
    cutUncertainty μ P z + cutUncertainty ν P z ≤ cutUncertainty (μ + ν) P z := by
  classical
  simp only [cutUncertainty, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro b _
  rw [measureReal_add_apply (by finiteness) (by finiteness),
    measureReal_add_apply (by finiteness) (by finiteness)]
  exact min_add_min_le_min_add_add

lemma uncertainty_complement (μ : Measure (V → Bool)) (P : Finset V) (z : V) :
    cutUncertainty (μ.map complementCut) P z = cutUncertainty μ P z := by
  classical
  simp only [cutUncertainty, map_measureReal_apply measurable_complementCut
    (cutEvent_measurable _ _ _ _), complement_preimage_event, Bool.not_false,
    Bool.not_true]
  simp_rw [min_comm]
  simpa only [complementEquiv, Equiv.coe_fn_mk] using (complementEquiv P).sum_comp
    (fun b : P → Bool => min (μ.real (cutEvent P z b false))
      (μ.real (cutEvent P z b true)))

lemma uncertainty_symmetrize (μ : Measure (V → Bool)) [IsFiniteMeasure μ]
    (P : Finset V) (z : V) :
    cutUncertainty μ P z ≤ cutUncertainty (symmetrizeCut μ) P z := by
  classical
  have h := uncertainty_add μ (μ.map complementCut) P z
  rw [uncertainty_complement] at h
  have heq : cutUncertainty (symmetrizeCut μ) P z =
      cutUncertainty (μ + μ.map complementCut) P z / 2 := by
    simp only [cutUncertainty, symmetrizeCut, measureReal_ennreal_smul_apply]
    norm_num
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro b _
    simp only [one_div_mul_eq_div, min_div_div_right (by norm_num : (0 : ℝ) ≤ 2)]
  rw [heq]
  linarith

lemma sweep_event (M : ℝ) (F : V → ℝ) (P : Finset V) (z : V)
    (b : P → Bool) (q : Bool) :
    (sweep M F).real (cutEvent P z b q) =
      volume.real ((thresholdLabels F ⁻¹' cutEvent P z b q) ∩ Icc (-M) M) := by
  rw [sweep, map_measureReal_apply (measurable_thresholdLabels F) (cutEvent_measurable ..),
    measureReal_restrict_apply ((measurable_thresholdLabels F) (cutEvent_measurable ..))]

end BoundedTreewidthL1

namespace BoundedTreewidthL1
open MeasureTheory Set
open scoped ENNReal
variable {V : Type*} [Fintype V]

lemma thresholdLabels_constant_gap
    {V : Type treewidthLevel1} [Fintype V]
    (F : V → ℝ) (z s : V) (t a : ℝ)
    (_ : 0 < t) (hs : t ≤ |F z - F s|)
    (ha : F z - t < a ∧ a < F z + t) :
    thresholdLabels F a s = thresholdLabels F (F z) s := by
  by_cases h : F z < F s
  · rw [abs_of_neg (sub_neg.mpr h)] at hs
    have h' : a < F s := by linarith
    simp [thresholdLabels, h, h']
  · rw [abs_of_nonneg (sub_nonneg.mpr (le_of_not_gt h))] at hs
    have h' : ¬a < F s := by linarith
    simp [thresholdLabels, h, h']

lemma sweep_height_gap_unsymmetrized (M : ℝ) (F : V → ℝ) (P : Finset V)
    (z : V) (t : ℝ) (ht : 0 < t) (hm : -M ≤ F z - t ∧ F z + t ≤ M)
    (hgap : ∀ s ∈ P, t ≤ |F z - F s|) :
    t ≤ cutUncertainty (sweep M F) P z := by
  classical
  let b : P → Bool := fun s => thresholdLabels F (F z) s
  have hfinite (q : Bool) :
      volume ((thresholdLabels F ⁻¹' cutEvent P z b q) ∩ Icc (-M) M) ≠ ⊤ :=
    measure_ne_top_of_subset Set.inter_subset_right (by rw [Real.volume_Icc]; finiteness)
  have hleft : Ioo (F z - t) (F z) ⊆
      (thresholdLabels F ⁻¹' cutEvent P z b true) ∩ Icc (-M) M := by
    rintro a ⟨hal, har⟩
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · intro s
      exact thresholdLabels_constant_gap F z s t a ht (hgap s s.property)
        ⟨hal, by linarith⟩
    · simp [thresholdLabels, har]
    · constructor <;> linarith [hm.1, hm.2]
  have hright : Ioo (F z) (F z + t) ⊆
      (thresholdLabels F ⁻¹' cutEvent P z b false) ∩ Icc (-M) M := by
    rintro a ⟨hal, har⟩
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · intro s
      exact thresholdLabels_constant_gap F z s t a ht (hgap s s.property)
        ⟨by linarith, har⟩
    · simp [thresholdLabels, show ¬a < F z by linarith]
    · constructor <;> linarith [hm.1, hm.2]
  have hl := measureReal_mono hleft (hfinite true)
  have hr := measureReal_mono hright (hfinite false)
  rw [Real.volume_real_Ioo_of_le (by linarith)] at hl
  rw [Real.volume_real_Ioo_of_le (by linarith)] at hr
  rw [← sweep_event] at hl hr
  have hmin : t ≤ min ((sweep M F).real (cutEvent P z b false))
      ((sweep M F).real (cutEvent P z b true)) := by
    apply le_min <;> linarith
  exact hmin.trans (Finset.single_le_sum
    (f := fun b : P → Bool => min ((sweep M F).real (cutEvent P z b false))
      ((sweep M F).real (cutEvent P z b true)))
    (fun _ _ => le_min measureReal_nonneg measureReal_nonneg) (Finset.mem_univ b))

theorem sweep_height_gap (M : ℝ) (F : V → ℝ) (P : Finset V) (z : V) (t : ℝ)
    (ht : 0 < t) (hm : -M ≤ F z - t ∧ F z + t ≤ M)
    (hgap : ∀ s ∈ P, t ≤ |F z - F s|) :
    t ≤ cutUncertainty (symmetrizeCut (sweep M F)) P z :=
  (sweep_height_gap_unsymmetrized M F P z t ht hm hgap).trans
    (uncertainty_symmetrize (sweep M F) P z)

end BoundedTreewidthL1

namespace BoundedTreewidthL1
open MeasureTheory Set
open scoped ENNReal
variable {V : Type*} [Fintype V]

lemma symmetrizeCut_add (μ ν : Measure (V → Bool)) :
    symmetrizeCut (μ + ν) = symmetrizeCut μ + symmetrizeCut ν := by
  simp only [symmetrizeCut, Measure.map_add _ _ measurable_complementCut, smul_add]
  ac_rfl

lemma sweep_pair_gap_ordered (M : ℝ) (F H : V → ℝ) (A : Finset V) (z : V)
    (hA : ∀ s ∈ A, F s = H s) (horder : F z ≤ H z)
    (hm : -M ≤ F z ∧ H z ≤ M) :
    H z - F z ≤ cutUncertainty (sweep M F + sweep M H) A z := by
  classical
  let E (b : A → Bool) : Set ℝ := Ioo (F z) (H z) ∩
    thresholdLabels F ⁻¹' {ω | ∀ s : A, ω s = b s}
  have hEm (b : A → Bool) : MeasurableSet (E b) :=
    measurableSet_Ioo.inter
      ((measurable_thresholdLabels F) (Set.toFinite _).measurableSet)
  have hEF (b : A → Bool) : E b ⊆
      (thresholdLabels F ⁻¹' cutEvent A z b false) ∩ Icc (-M) M := by
    rintro a ⟨⟨hal, har⟩, hb⟩
    refine ⟨⟨hb, ?_⟩, ?_⟩
    · simp [thresholdLabels, show ¬a < F z by linarith]
    · constructor <;> linarith [hm.1, hm.2]
  have hEH (b : A → Bool) : E b ⊆
      (thresholdLabels H ⁻¹' cutEvent A z b true) ∩ Icc (-M) M := by
    rintro a ⟨⟨hal, har⟩, hb⟩
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · intro s
      change decide (a < H s) = b s
      rw [← hA s s.property]
      exact hb s
    · simp [thresholdLabels, har]
    · constructor <;> linarith [hm.1, hm.2]
  have hfinF (b : A → Bool) : volume
      ((thresholdLabels F ⁻¹' cutEvent A z b false) ∩ Icc (-M) M) ≠ ⊤ :=
    measure_ne_top_of_subset Set.inter_subset_right (by rw [Real.volume_Icc]; finiteness)
  have hfinH (b : A → Bool) : volume
      ((thresholdLabels H ⁻¹' cutEvent A z b true) ∩ Icc (-M) M) ≠ ⊤ :=
    measure_ne_top_of_subset Set.inter_subset_right (by rw [Real.volume_Icc]; finiteness)
  have hfinE (b : A → Bool) : volume (E b) ≠ ⊤ :=
    measure_ne_top_of_subset (hEF b) (hfinF b)
  have hdis : Pairwise (Function.onFun Disjoint E) := by
    intro b c hbc
    apply Set.disjoint_left.mpr
    intro a hb hc
    apply hbc
    funext s
    exact (hb.2 s).symm.trans (hc.2 s)
  have hcover : (⋃ b : A → Bool, E b) = Ioo (F z) (H z) := by
    ext a
    constructor
    · intro ha
      obtain ⟨b, hb⟩ := Set.mem_iUnion.mp ha
      exact hb.1
    · intro ha
      exact Set.mem_iUnion.mpr ⟨fun s => thresholdLabels F a s, ha, fun _ => rfl⟩
  have hsum := measureReal_iUnion_fintype hdis hEm hfinE
  rw [hcover, Real.volume_real_Ioo_of_le horder] at hsum
  rw [hsum, cutUncertainty]
  apply Finset.sum_le_sum
  intro b _
  have hF := measureReal_mono (hEF b) (hfinF b)
  have hH := measureReal_mono (hEH b) (hfinH b)
  rw [← sweep_event] at hF hH
  rw [measureReal_add_apply (by finiteness) (by finiteness),
    measureReal_add_apply (by finiteness) (by finiteness)]
  apply le_min
  · exact hF.trans (le_add_of_nonneg_right measureReal_nonneg)
  · exact hH.trans (le_add_of_nonneg_left measureReal_nonneg)

theorem sweep_launch_gap (M : ℝ) (f g : V → ℝ) (A : Finset V)
    (hg : ∀ s ∈ A, g s = 0)
    (hm : ∀ v, |f v + g v| ≤ M ∧ |f v - g v| ≤ M) (z : V) :
    2 * |g z| ≤ cutUncertainty
      (symmetrizeCut (sweep M (fun v => f v + g v)) +
       symmetrizeCut (sweep M (fun v => f v - g v))) A z := by
  classical
  rw [← symmetrizeCut_add]
  apply le_trans _ (uncertainty_symmetrize _ A z)
  have hA : ∀ s ∈ A, f s - g s = f s + g s := by
    intro s hs
    rw [hg s hs]
    ring
  rcases le_total 0 (g z) with h | h
  · have hgap := sweep_pair_gap_ordered M (fun v => f v - g v)
      (fun v => f v + g v) A z hA (by linarith)
      ⟨(abs_le.mp (hm z).2).1, (abs_le.mp (hm z).1).2⟩
    calc
      2 * |g z| = (f z + g z) - (f z - g z) := by rw [abs_of_nonneg h]; ring
      _ ≤ _ := by
        rw [add_comm (sweep M (fun v => f v + g v))
          (sweep M (fun v => f v - g v))]
        exact hgap
  · have hgap := sweep_pair_gap_ordered M (fun v => f v + g v)
      (fun v => f v - g v) A z (fun s hs => (hA s hs).symm) (by linarith)
      ⟨(abs_le.mp (hm z).1).1, (abs_le.mp (hm z).2).2⟩
    calc
      2 * |g z| = (f z - g z) - (f z + g z) := by rw [abs_of_nonpos h]; ring
      _ ≤ _ := hgap

end BoundedTreewidthL1

namespace BoundedTreewidthL1
open MeasureTheory Set
open scoped ENNReal
variable {V : Type*} [Fintype V]

noncomputable def cutTrace (μ : Measure (V → Bool)) (P : Finset V) : Measure (P → Bool) :=
  μ.map (fun ω s => ω s)

noncomputable def cutSeparation (μ : Measure (V → Bool)) (u v : V) : ℝ :=
  μ.real {ω | ω u ≠ ω v}

def CommonWeakOrder (P : Finset V) (F H : V → ℝ) : Prop :=
  ∃ e : Fin P.card ≃ P,
    Monotone (fun i => F (e i)) ∧ Monotone (fun i => H (e i))

def partialCutEvent (P Q : Finset V) : Set (V → Bool) :=
  {ω | (∀ p ∈ P, ω p = true) ∧ ∀ q ∈ Q, ω q = false}

/-- On a finite Boolean cube, all-true conjunctions determine a finite measure.
The proof retains the total mass (the conjunction over the empty set). -/
lemma cutMeasure_ext_all_true (μ ν : Measure (V → Bool)) [IsFiniteMeasure μ]
    [IsFiniteMeasure ν]
    (heq : ∀ P : Finset V, μ.real {ω | ∀ p ∈ P, ω p = true} =
      ν.real {ω | ∀ p ∈ P, ω p = true}) : μ = ν := by
  classical
  have hpartial (Q : Finset V) : ∀ P : Finset V,
      μ.real (partialCutEvent P Q) = ν.real (partialCutEvent P Q) := by
    induction Q using Finset.induction_on with
    | empty =>
      intro P
      simpa [partialCutEvent] using heq P
    | @insert a Q ha ih =>
      intro P
      have hpart : partialCutEvent P Q =
          partialCutEvent (insert a P) Q ∪ partialCutEvent P (insert a Q) := by
        ext ω
        simp only [partialCutEvent, Set.mem_ofPred_eq, Finset.mem_insert,
          forall_eq_or_imp, Set.mem_union]
        cases h : ω a <;> simp
      have hdis : Disjoint (partialCutEvent (insert a P) Q)
          (partialCutEvent P (insert a Q)) := by
        apply Set.disjoint_left.mpr
        intro ω h₁ h₂
        have ht := h₁.1 a (Finset.mem_insert_self a P)
        have hf := h₂.2 a (Finset.mem_insert_self a Q)
        simp_all
      have hμ := measureReal_union hdis
        (Set.toFinite (partialCutEvent P (insert a Q))).measurableSet
        (μ := μ)
      have hν := measureReal_union hdis
        (Set.toFinite (partialCutEvent P (insert a Q))).measurableSet
        (μ := ν)
      rw [← hpart] at hμ hν
      linarith [ih P, ih (insert a P)]
  apply Measure.ext_of_singleton
  intro ω
  have hs : ({ω} : Set (V → Bool)) = partialCutEvent
      (Finset.univ.filter fun v => ω v = true)
      (Finset.univ.filter fun v => ω v = false) := by
    ext η
    simp only [Set.mem_singleton_iff, partialCutEvent, Set.mem_ofPred_eq,
      Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro rfl
      exact ⟨fun _ h => h, fun _ h => h⟩
    · rintro ⟨h₁, h₂⟩
      funext v
      cases h : ω v
      · exact h₂ v h
      · exact h₁ v h
  apply (measureReal_eq_measureReal_iff (by finiteness) (by finiteness)).mp
  rw [hs]
  exact hpartial _ _

lemma sweep_all_true_of_min (M : ℝ) (F : V → ℝ) (P : Finset V)
    (a : V) (ha : a ∈ P) (hmin : ∀ p ∈ P, F a ≤ F p)
    (hm : -M ≤ F a ∧ F a ≤ M) :
    (sweep M F).real {ω | ∀ p ∈ P, ω p = true} = F a + M := by
  rw [sweep, map_measureReal_apply (measurable_thresholdLabels F)
    (Set.toFinite _).measurableSet,
    measureReal_restrict_apply ((measurable_thresholdLabels F) (Set.toFinite _).measurableSet)]
  have hset : (thresholdLabels F ⁻¹' {ω | ∀ p ∈ P, ω p = true}) ∩ Icc (-M) M =
      Ico (-M) (F a) := by
    ext t
    constructor
    · rintro ⟨h, hM⟩
      exact ⟨hM.1, of_decide_eq_true (h a ha)⟩
    · rintro ⟨hl, hr⟩
      refine ⟨?_, ⟨hl, le_trans hr.le hm.2⟩⟩
      intro p hp
      exact decide_eq_true (hr.trans_le (hmin p hp))
  rw [hset, Real.volume_real_Ico_of_le hm.1]
  ring

lemma sweep_total_mass (M : ℝ) (hM : 0 ≤ M) (F : V → ℝ) :
    (sweep M F).real Set.univ = 2 * M := by
  rw [sweep, map_measureReal_apply (measurable_thresholdLabels F) MeasurableSet.univ]
  simp only [Set.preimage_univ, measureReal_restrict_apply_univ]
  rw [Real.volume_real_Icc_of_le (by linarith)]
  ring

end BoundedTreewidthL1

namespace BoundedTreewidthL1
open MeasureTheory Set
open scoped ENNReal
variable {V : Type*} [Fintype V]

lemma sweep_affine_of_common_min (M : ℝ) (hM : 0 ≤ M) (F H : V → ℝ)
    (hF : ∀ v, |F v| ≤ M) (hH : ∀ v, |H v| ≤ M)
    (hmin : ∀ P : Finset V, P.Nonempty →
      ∃ a ∈ P, ∀ p ∈ P, F a ≤ F p ∧ H a ≤ H p) :
    sweep M F + sweep M H =
      sweep M (fun v => (F v + H v) / 2) + sweep M (fun v => (F v + H v) / 2) := by
  classical
  apply cutMeasure_ext_all_true
  intro P
  rw [measureReal_add_apply (by finiteness) (by finiteness),
    measureReal_add_apply (by finiteness) (by finiteness)]
  by_cases hP : P.Nonempty
  · obtain ⟨a, ha, ham⟩ := hmin P hP
    have haF := abs_le.mp (hF a)
    have haH := abs_le.mp (hH a)
    rw [sweep_all_true_of_min M F P a ha (fun p hp => (ham p hp).1) haF,
      sweep_all_true_of_min M H P a ha (fun p hp => (ham p hp).2) haH,
      sweep_all_true_of_min M (fun v => (F v + H v) / 2) P a ha
        (by intro p hp; linarith [(ham p hp).1, (ham p hp).2])
        (by constructor <;> linarith)]
    ring
  · have hPe : P = ∅ := Finset.not_nonempty_iff_eq_empty.mp hP
    have hevent : {ω : V → Bool | ∀ p ∈ (∅ : Finset V), ω p = true} = univ := by
      ext ω
      simp
    rw [hPe, hevent, sweep_total_mass M hM, sweep_total_mass M hM, sweep_total_mass M hM]

lemma cutTrace_add (μ ν : Measure (V → Bool)) (P : Finset V) :
    cutTrace (μ + ν) P = cutTrace μ P + cutTrace ν P := by
  exact Measure.map_add _ _ (measurable_of_finite _)

lemma cutTrace_sweep (M : ℝ) (F : V → ℝ) (P : Finset V) :
    cutTrace (sweep M F) P = sweep M (fun p : P => F p) := by
  rw [cutTrace, sweep, Measure.map_map (measurable_of_finite _) (measurable_thresholdLabels F)]
  rfl

theorem sweep_trace_update (M : ℝ) (hM : 0 < M) (F H g : V → ℝ) (P : Finset V)
    (horder : CommonWeakOrder P F H) (hg : ∀ s ∈ P, g s = 0)
    (hF : ∀ v, |F v| ≤ M) (hH : ∀ v, |H v| ≤ M)
    (_ : ∀ v, |(F v + H v) / 2 + g v| ≤ M)
    (_ : ∀ v, |(F v + H v) / 2 - g v| ≤ M) :
    cutTrace (sweep M F + sweep M H) P =
      cutTrace (sweep M (fun v => (F v + H v) / 2 + g v) +
        sweep M (fun v => (F v + H v) / 2 - g v)) P := by
  classical
  simp only [cutTrace_add, cutTrace_sweep]
  have hp' : (fun p : P => (F p + H p) / 2 + g p) =
      (fun p : P => (F p + H p) / 2) := by
    funext p
    rw [hg p p.property, add_zero]
  have hn' : (fun p : P => (F p + H p) / 2 - g p) =
      (fun p : P => (F p + H p) / 2) := by
    funext p
    rw [hg p p.property, sub_zero]
  rw [hp', hn']
  apply sweep_affine_of_common_min M hM.le (fun p : P => F p) (fun p : P => H p)
    (fun p => hF p) (fun p => hH p)
  intro S hS
  obtain ⟨e, heF, heH⟩ := horder
  obtain ⟨a, ha, hmina⟩ := Finset.exists_min_image S (fun p => e.symm p) hS
  refine ⟨a, ha, ?_⟩
  intro p hp
  simpa only [Equiv.apply_symm_apply] using
    And.intro (heF (hmina p hp)) (heH (hmina p hp))

lemma sweep_separation_ordered (M : ℝ) (F : V → ℝ) (u v : V)
    (h : F u ≤ F v) (hm : -M ≤ F u ∧ F v ≤ M) :
    cutSeparation (sweep M F) u v = F v - F u := by
  rw [cutSeparation, sweep, map_measureReal_apply (measurable_thresholdLabels F)
    (Set.toFinite _).measurableSet,
    measureReal_restrict_apply ((measurable_thresholdLabels F) (Set.toFinite _).measurableSet)]
  have hset : (thresholdLabels F ⁻¹' {ω | ω u ≠ ω v}) ∩ Icc (-M) M =
      Ico (F u) (F v) := by
    ext t
    constructor
    · rintro ⟨hne, _⟩
      by_cases hu : t < F u
      · have hv : t < F v := hu.trans_le h
        simp [thresholdLabels, hu, hv] at hne
      · have hv : t < F v := by
          by_contra hv
          simp [thresholdLabels, hu, hv] at hne
        exact ⟨le_of_not_gt hu, hv⟩
    · rintro ⟨hu, hv⟩
      refine ⟨?_, ⟨hm.1.trans hu, hv.le.trans hm.2⟩⟩
      simp [thresholdLabels, show ¬t < F u from not_lt.mpr hu, hv]
  rw [hset, Real.volume_real_Ico_of_le h]

theorem sweep_separation (M : ℝ) (F : V → ℝ) (hF : ∀ v, |F v| ≤ M) (u v : V) :
    cutSeparation (sweep M F) u v = |F u - F v| := by
  rcases le_total (F u) (F v) with h | h
  · rw [sweep_separation_ordered M F u v h
      ⟨(abs_le.mp (hF u)).1, (abs_le.mp (hF v)).2⟩,
      abs_of_nonpos (sub_nonpos.mpr h)]
    ring
  · have he : cutSeparation (sweep M F) u v = cutSeparation (sweep M F) v u := by
      unfold cutSeparation
      congr 1
      ext ω
      exact ne_comm
    rw [he, sweep_separation_ordered M F v u h
      ⟨(abs_le.mp (hF v)).1, (abs_le.mp (hF u)).2⟩,
      abs_of_nonneg (sub_nonneg.mpr h)]

end BoundedTreewidthL1

end OAI
