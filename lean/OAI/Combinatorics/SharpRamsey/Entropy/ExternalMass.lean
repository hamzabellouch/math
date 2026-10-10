import Mathlib
import OAI.Combinatorics.SharpRamsey.Entropy.ForcedHits

namespace OAI

/-! High moments, finite-field subspaces, and incidence bounds. -/

section
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace SharpRamseyFive.PoissonScore
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {κ : Type*}
variable {κ : Type*} [Fintype κ] [DecidableEq κ]
section ComponentGeometry
variable {H : Type*} [Fintype H] [DecidableEq H]
omit [Fintype ι] in
lemma external_mass_le (rate : ι → ℝ≥0) (s : H → Finset ι)
    {t : ℝ} (ht : 0 ≤ t) (h : H) :
    mass rate (externalPart rate s t h) ≤ (Fintype.card H - 1 : ℕ) * t := by
  classical
  let K := otherComponents rate s t h
  have hK : K ⊆ Finset.univ.erase h := by
    intro k hk
    simp only [K, otherComponents, Finset.mem_filter, Finset.mem_univ, true_and] at hk
    simp only [Finset.mem_erase, Finset.mem_univ, and_true]
    intro he
    subst k
    exact hk rfl
  have hc : K.card ≤ Fintype.card H - 1 := by
    simpa only [Finset.card_erase_of_mem (Finset.mem_univ h), Finset.card_univ] using
      Finset.card_le_card hK
  calc
    _ ≤ ∑ k ∈ K, mass rate (s h ∩ s k) := external_mass_le_sum rate s t h
    _ ≤ K.card * t := by
      simpa only [nsmul_eq_mul] using Finset.sum_le_card_nsmul K
        (fun k => mass rate (s h ∩ s k)) t (by
          intro k hk
          apply cross_component_overlap rate s t
          simpa only [K, otherComponents, Finset.mem_filter, Finset.mem_univ, true_and] using hk)
    _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast hc) ht

omit [Fintype ι] in

lemma internal_mass_lower (rate : ι → ℝ≥0) (s : H → Finset ι)
    {t c : ℝ} (ht : 0 ≤ t) (hs : ∀ h, c ≤ mass rate (s h)) (h : H) :
    c - (Fintype.card H - 1 : ℕ) * t ≤ mass rate (internalPart rate s t h) := by
  have := external_mass_le rate s ht h
  have := internal_external_mass rate s t h
  have := hs h
  linarith

omit [Fintype ι] [Fintype H] [DecidableEq H] in
lemma internal_parts_disjoint (rate : ι → ℝ≥0) (s : H → Finset ι)
    (t : ℝ) {h k : H} (hc : (strongGraph rate s t).connectedComponentMk h ≠
      (strongGraph rate s t).connectedComponentMk k) :
    Disjoint (internalPart rate s t h) (internalPart rate s t k) := by
  classical
  apply Finset.disjoint_left.mpr
  intro i hi hk
  simp only [internalPart, Finset.mem_filter] at hi hk
  exact hi.2 ⟨h, k, hi.1, hk.1, hc⟩

noncomputable def componentLabel (rate : ι → ℝ≥0) (s : H → Finset ι)
    (t : ℝ) (i : ι) : Option (strongGraph rate s t).ConnectedComponent := by
  classical
  exact if hi : ∃ h, i ∈ s h then
    if External rate s t i then none else
      some ((strongGraph rate s t).connectedComponentMk hi.choose)
    else none

omit [Fintype ι] [DecidableEq H] in
lemma componentLabel_external (rate : ι → ℝ≥0) (s : H → Finset ι)
    (t : ℝ) {i : ι} (hi : External rate s t i) :
    componentLabel rate s t i = none := by
  classical
  simp only [componentLabel, hi, ↓reduceIte]
  split_ifs <;> rfl

omit [Fintype ι] [DecidableEq H] in
lemma componentLabel_internal (rate : ι → ℝ≥0) (s : H → Finset ι)
    (t : ℝ) {h : H} {i : ι} (hi : i ∈ internalPart rate s t h) :
    componentLabel rate s t i = some ((strongGraph rate s t).connectedComponentMk h) := by
  classical
  simp only [internalPart, Finset.mem_filter] at hi
  have hex : ∃ k, i ∈ s k := ⟨h, hi.1⟩
  have he := hex.choose_spec
  have hc : (strongGraph rate s t).connectedComponentMk hex.choose =
      (strongGraph rate s t).connectedComponentMk h := by
    by_contra hn
    exact hi.2 ⟨hex.choose, h, he, hi.1, hn⟩
  simp only [componentLabel, dite_eq_left hex, ite_eq_right hi.2, hc]
omit [Fintype ι] [DecidableEq H] in

lemma internalPart_iff_label (rate : ι → ℝ≥0) (s : H → Finset ι)
    (t : ℝ) (h : H) (i : ι) :
    i ∈ internalPart rate s t h ↔ i ∈ s h ∧
      componentLabel rate s t i = some ((strongGraph rate s t).connectedComponentMk h) := by
  classical
  constructor
  · intro hi
    exact ⟨(Finset.mem_filter.mp hi).1, componentLabel_internal rate s t hi⟩
  · rintro ⟨hi, he⟩
    apply Finset.mem_filter.mpr
    refine ⟨hi, ?_⟩
    intro hn
    rw [componentLabel_external rate s t hn] at he
    cases he

omit [Fintype ι] [DecidableEq H] in

lemma direction_internal_or_external (rate : ι → ℝ≥0) (s : H → Finset ι)
    (t : ℝ) {h : H} {i : ι} (hi : i ∈ s h) :
    componentLabel rate s t i = none ∨
      componentLabel rate s t i = some ((strongGraph rate s t).connectedComponentMk h) := by
  classical
  by_cases he : External rate s t i
  · exact Or.inl (componentLabel_external rate s t he)
  · exact Or.inr (componentLabel_internal rate s t (Finset.mem_filter.mpr ⟨hi, he⟩))
omit [Fintype ι] in

lemma source_internal_mass_lower (rate : ι → ℝ≥0) (s : H → Finset ι)
    {p : ℕ} (hp : 0 < p) (hc : Fintype.card H ≤ p)
    (hs : ∀ h, (3 / 4 : ℝ) ≤ mass rate (s h)) (h : H) :
    (37 / 50 : ℝ) ≤ mass rate (internalPart rate s (1 / (100 * p)) h) := by
  have ht : (0 : ℝ) ≤ 1 / (100 * p : ℝ) := by positivity
  have hl := internal_mass_lower rate s ht hs h
  have hh : (0 : ℝ) < p := by exact_mod_cast hp
  have hcard : ((Fintype.card H - 1 : ℕ) : ℝ) ≤ (p : ℝ) := by
    exact_mod_cast ((Nat.sub_le (Fintype.card H) 1).trans hc)
  have hm : ((Fintype.card H - 1 : ℕ) : ℝ) * (1 / (100 * p)) ≤ (1 / 100 : ℝ) := by
    calc
      _ ≤ (p : ℝ) * (1 / (100 * p)) := mul_le_mul_of_nonneg_right hcard ht
      _ = _ := by field_simp
  linarith

end ComponentGeometry

end SharpRamseyFive.PoissonScore

namespace SharpRamseyFive.TupleComponents
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
open SharpRamseyFive.PoissonScore
open Classical
variable {D V C : Type} [Fintype D] [DecidableEq D]
  [Fintype V] [DecidableEq V] [Fintype C] [DecidableEq C]
variable (label : D → Option C) (R : ℕ)

abbrev Block (c : Option C) := {i : Fin R × D // label i.2 = c}
noncomputable def fill (c : C) (z : Block label R none → ℕ)
    (x : Block label R (some c) → ℕ) (r : Fin R) (d : D) : ℕ :=
  if he : label d = none then z ⟨(r,d), he⟩ else
    if hi : label d = some c then x ⟨(r,d), hi⟩ else 0

omit [Fintype D] [DecidableEq D] [Fintype C] in
lemma fill_restrict (c : C) (ω : Fin R × D → ℕ) {d : D}
    (hd : label d = none ∨ label d = some c) (r : Fin R) :
    fill label R c (fun i => ω i) (fun i => ω i) r d = ω (r,d) := by
  rcases hd with hd | hd <;> simp [fill, hd]

noncomputable def lineTrunc (J : ℕ) (ω : Fin R → ℕ) : ℝ :=
  if (Finset.univ.filter (fun r => ω r ≠ 0)).card < J then 1 else 0

noncomputable def blockTrunc (J : ℕ) (c : Option C) (ω : Block label R c → ℕ) : ℝ :=
  ∏ d : {d : D // label d = c}, lineTrunc R J (fun r => ω ⟨(r,d), d.property⟩)

lemma lineTrunc_range (J : ℕ) (ω : Fin R → ℕ) :
    lineTrunc R J ω ∈ Set.Icc (0 : ℝ) 1 := by unfold lineTrunc; split_ifs <;> norm_num

omit [DecidableEq D] [Fintype C] in
lemma blockTrunc_range (J : ℕ) (c : Option C) (ω : Block label R c → ℕ) :
    blockTrunc label R J c ω ∈ Set.Icc (0 : ℝ) 1 := by
  constructor
  · exact Finset.prod_nonneg (fun _ _ => (lineTrunc_range R J _).1)
  · exact Finset.prod_le_one₀ (fun _ _ => (lineTrunc_range R J _).1)
      (fun _ _ => (lineTrunc_range R J _).2)

lemma prod_fibers {A K : Type} [Fintype A] [Fintype K] [DecidableEq K]
    (col : A → K) (f : A → ℝ) :
    (∏ c : K, ∏ a : {a : A // col a = c}, f a) = ∏ a, f a := by
  classical
  calc
    _ = ∏ c : K, ∏ a ∈ Finset.univ.filter (fun a => col a = c), f a := by
      apply Finset.prod_congr rfl
      intro c _
      symm
      exact Finset.prod_subtype _ (by simp) f
    _ = _ := by
      simpa using Finset.prod_fiberwise Finset.univ col f

omit [DecidableEq D] in
lemma trunc_split (J : ℕ) (ω : Fin R × D → ℕ) :
    (∏ d : D, lineTrunc R J (fun r => ω (r,d))) =
      blockTrunc label R J none (fun i => ω i) *
        ∏ c : C, blockTrunc label R J (some c) (fun i => ω i) := by
  rw [← Fintype.prod_option (fun c => blockTrunc label R J c (fun i => ω i))]
  exact (prod_fibers label (fun d => lineTrunc R J (fun r => ω (r,d)))).symm

omit [Fintype D] [DecidableEq D] in
lemma emptyIndicator_congr (s : Finset D) (ω ν : D → ℕ)
    (he : ∀ d ∈ s, ω d = ν d) : emptyIndicator s ω = emptyIndicator s ν := by
  have h : ω ∈ emptyEvent s ↔ ν ∈ emptyEvent s := by
    simp only [emptyEvent, Set.mem_pi, Set.mem_singleton_iff, Finset.mem_coe]
    exact forall₂_congr (fun d hd => by rw [he d hd])
  by_cases hω : ω ∈ emptyEvent s
  · simp [emptyIndicator, hω, h.mp hω]
  · simp [emptyIndicator, hω, (not_congr h).mp hω]
omit [Fintype D] [DecidableEq D] in

lemma scoreTerm_congr (s : Finset D) (b : ℝ) (own : Fin R → Bool)
    (ω ν : Fin R → D → ℕ) (he : ∀ r d, d ∈ s → ω r d = ν r d) :
    scoreTerm s b own ω = scoreTerm s b own ν := by
  unfold scoreTerm
  apply Finset.prod_congr rfl
  intro r _
  simp only [centeredFactor, emptyIndicator_congr s (ω r) (ν r) (he r)]

variable (color : V → C) (s : V → Finset D) (b : ℝ) (own : V → Fin R → Bool)

noncomputable def componentFactor (J : ℕ) (c : C)
    (z : Block label R none → ℕ) (x : Block label R (some c) → ℕ) : ℝ :=
  blockTrunc label R J (some c) x *
    ∏ v : {v : V // color v = c}, scoreTerm (s v) b (own v) (fill label R c z x)

omit [DecidableEq V] in
omit [Fintype C] in
omit [DecidableEq D] in
lemma componentFactor_bound (J : ℕ) (hb : b ∈ Set.Icc (0 : ℝ) 1) (c : C)
    (z : Block label R none → ℕ) (x : Block label R (some c) → ℕ) :
    |componentFactor label R color s b own J c z x| ≤ 1 := by
  rw [componentFactor, abs_mul, Finset.abs_prod]
  have htrunc : |blockTrunc label R J (some c) x| ≤ 1 := by
    rw [abs_of_nonneg (blockTrunc_range label R J (some c) x).1]
    exact (blockTrunc_range label R J (some c) x).2
  refine (mul_le_of_le_one_left (Finset.prod_nonneg (fun _ _ => abs_nonneg _))
    htrunc).trans ?_
  apply Finset.prod_le_one₀ (fun _ _ => abs_nonneg _)
  intro vertex _
  simpa only [maskedTerm, maskedFactor, Bool.false_eq_true, ↓reduceIte, scoreTerm]
    using abs_maskedTerm_le_one (s vertex) hb (own vertex) (fun _ => false)
      (fill label R c z x)

omit [DecidableEq V] in
omit [DecidableEq D] in
lemma tuple_pointwise_split (J : ℕ)
    (hcompat : ∀ v d, d ∈ s v → label d = none ∨ label d = some (color v))
    (ω : Fin R × D → ℕ) :
    (∏ d : D, lineTrunc R J (fun r => ω (r,d))) *
        (∏ v : V, scoreTerm (s v) b (own v) (fun r d => ω (r,d))) =
      blockTrunc label R J none (fun i => ω i) *
        ∏ c : C, componentFactor label R color s b own J c
          (fun i => ω i) (fun i => ω i) := by
  have he (c : C) (v : {v : V // color v = c}) :
      scoreTerm (s v) b (own v)
        (fill label R c (fun i => ω i) (fun i => ω i)) =
      scoreTerm (s v) b (own v) (fun r d => ω (r,d)) := by
    apply scoreTerm_congr R
    intro r d hd
    apply fill_restrict label R c ω _ r
    simpa only [v.property] using hcompat v d hd
  simp_rw [componentFactor, he]
  rw [Finset.prod_mul_distrib, prod_fibers color (fun v => scoreTerm (s v) b (own v) (fun r d => ω (r,d)))]
  rw [trunc_split label R J ω]
  ring

omit [DecidableEq V] in
omit [DecidableEq D] in

theorem tuple_integral_split (rate : D → ℝ≥0) (J : ℕ)
    (hb : b ∈ Set.Icc (0 : ℝ) 1)
    (hcompat : ∀ v d, d ∈ s v → label d = none ∨ label d = some (color v)) :
    (∫ ω, (∏ d : D, lineTrunc R J (fun r => ω (r,d))) *
        (∏ v : V, scoreTerm (s v) b (own v) (fun r d => ω (r,d)))
      ∂batchMeasure (fun i : Fin R × D => rate i.2)) =
      ∫ z, blockTrunc label R J none z * ∏ c : C,
        ∫ x, componentFactor label R color s b own J c z x
          ∂batchMeasure (fun i : Block label R (some c) => rate i.1.2)
        ∂batchMeasure (fun i : Block label R none => rate i.1.2) := by
  have he := integral_external_components (fun i : Fin R × D => rate i.2)
    (fun i => label i.2) (blockTrunc label R J none)
    (componentFactor label R color s b own J)
    (fun z => by rw [abs_of_nonneg (blockTrunc_range label R J none z).1];
                 exact (blockTrunc_range label R J none z).2)
    (componentFactor_bound label R color s b own J hb)
  rw [← he]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (tuple_pointwise_split label R color s b own J hcompat)

noncomputable def strongSplit (weight rate : D → ℝ≥0) (t : ℝ) (J : ℕ) : ℝ := by
  classical
  let G := strongGraph weight s t
  let label := componentLabel weight s t
  exact ∫ z, blockTrunc label R J none z * ∏ c : G.ConnectedComponent,
    ∫ x, componentFactor label R G.connectedComponentMk s b own J c z x
      ∂batchMeasure (fun i : Block label R (some c) => rate i.1.2)
      ∂batchMeasure (fun i : Block label R none => rate i.1.2)

lemma strong_tuple_integral_split (weight rate : D → ℝ≥0) (t : ℝ) (J : ℕ)
    (hb : b ∈ Set.Icc (0 : ℝ) 1) :
    (∫ ω, (∏ d : D, lineTrunc R J (fun r => ω (r,d))) *
        (∏ v : V, scoreTerm (s v) b (own v) (fun r d => ω (r,d)))
      ∂batchMeasure (fun i : Fin R × D => rate i.2)) =
      strongSplit R s b own weight rate t J := by
  classical
  unfold strongSplit
  apply tuple_integral_split _ R _ s b own rate J hb
  intro v d hd
  exact direction_internal_or_external weight s t hd

abbrev IntDir (c : C) := {d : D // label d = some c}

noncomputable def inside (c : C) (S : Finset D) : Finset (IntDir label c) :=
  Finset.univ.filter (fun d => d.val ∈ S)

noncomputable def touched (_c : C) (S : Finset D) (z : Block label R none → ℕ)
    (r : Fin R) : Bool :=
  decide (∃ d : {d : D // label d = none}, d.val ∈ S ∧ z ⟨(r,d), d.property⟩ ≠ 0)

noncomputable def unblock (c : C) (x : Block label R (some c) → ℕ) :
    Fin R → IntDir label c → ℕ := fun r d => x ⟨(r,d), d.property⟩

omit [Fintype C] in
lemma fill_empty_iff (c : C) (S : Finset D)
    (hc : ∀ d ∈ S, label d = none ∨ label d = some c)
    (z : Block label R none → ℕ) (x : Block label R (some c) → ℕ) (r : Fin R) :
    fill label R c z x r ∈ emptyEvent S ↔
      touched label R c S z r = false ∧
        unblock label R c x r ∈ emptyEvent (inside label c S) := by
  simp only [emptyEvent, Set.mem_pi, Set.mem_singleton_iff, Finset.mem_coe]
  constructor
  · intro h
    constructor
    · simp only [touched, decide_eq_false_iff_not, not_exists, not_and]
      intro d hd
      have := h d hd
      simpa [fill, d.property] using this
    · intro d hd
      have := h d (Finset.mem_filter.mp hd).2
      simpa [fill, d.property, unblock] using this
  · rintro ⟨he, hi⟩ d hd
    rcases hc d hd with hd0 | hdc
    · have hz : z ⟨(r,d), hd0⟩ = 0 := by
        have he' : ¬ ∃ d : {d : D // label d = none},
            d.val ∈ S ∧ z ⟨(r,d), d.property⟩ ≠ 0 := by
          simpa only [touched, decide_eq_false_iff_not] using he
        by_contra hn
        exact he' ⟨⟨d,hd0⟩, hd, hn⟩
      simpa [fill, hd0] using hz
    · have hz := hi ⟨d,hdc⟩ (by simp [inside, hd])
      simpa [fill, hdc, unblock] using hz
omit [Fintype C] in

lemma scoreTerm_eq_masked (c : C) (S : Finset D) (B : ℝ) (o : Fin R → Bool)
    (hc : ∀ d ∈ S, label d = none ∨ label d = some c)
    (z : Block label R none → ℕ) (x : Block label R (some c) → ℕ) :
    scoreTerm S B o (fill label R c z x) =
      maskedTerm (inside label c S) B o (touched label R c S z) (unblock label R c x) := by
  apply Finset.prod_congr rfl
  intro r _
  have hh := fill_empty_iff label R c S hc z x r
  cases ho : o r <;> simp only [maskedFactor, Bool.false_eq_true, ↓reduceIte]
  by_cases he : touched label R c S z r = true
  · have hn : fill label R c z x r ∉ emptyEvent S := by simpa [he] using hh
    simp [he, centeredFactor, emptyIndicator, hn]
  · have ht : touched label R c S z r = false := Bool.eq_false_of_not_eq_true he
    simp only [ht, true_and] at hh
    by_cases hi : unblock label R c x r ∈ emptyEvent (inside label c S)
    · simp [ht, centeredFactor, emptyIndicator, hi, hh.mpr hi]
    · simp [ht, centeredFactor, emptyIndicator, hi, (not_congr hh).mpr hi]

noncomputable def blockCoords (c : C) : (Fin R × IntDir label c) ≃ Block label R (some c) where
  toFun i := ⟨(i.1,i.2), i.2.property⟩
  invFun i := (i.1.1, ⟨i.1.2, i.property⟩)
  left_inv _ := rfl
  right_inv _ := rfl

noncomputable def unblockEquiv (c : C) :
    (Block label R (some c) → ℕ) ≃ᵐ (Fin R → IntDir label c → ℕ) :=
  (MeasurableEquiv.piCongrLeft (fun _ : Block label R (some c) => ℕ)
    (blockCoords label R c)).symm.trans (MeasurableEquiv.curry (Fin R) (IntDir label c) ℕ)

omit [Fintype D] [DecidableEq D] [Fintype C] [DecidableEq C] in
@[simp] lemma unblockEquiv_apply (c : C) (x : Block label R (some c) → ℕ) :
    unblockEquiv label R c x = unblock label R c x := rfl

omit [Fintype C] in
omit [DecidableEq D] in
lemma measurePreserving_unblock (rate : D → ℝ≥0) (c : C) :
    MeasurePreserving (unblockEquiv label R c)
      (batchMeasure (fun i : Block label R (some c) => rate i.1.2))
      (scheduleMeasure (fun d : IntDir label c => rate d) R) := by
  exact (measurePreserving_uncurry_schedule (fun d : IntDir label c => rate d) R).symm.comp
    (measurePreserving_piCongrLeft
      (fun i : Block label R (some c) => poissonMeasure (rate i.1.2))
      (blockCoords label R c)).symm

omit [DecidableEq D] [Fintype C] in
lemma integrable_block_bounded (rate : D → ℝ≥0) (c : Option C)
    (f : (Block label R c → ℕ) → ℝ) (h : ∀ x, |f x| ≤ 1) :
    Integrable f (batchMeasure (fun i : Block label R c => rate i.1.2)) := by
  apply Integrable.of_bound (measurable_of_countable f).aestronglyMeasurable 1
  exact Filter.Eventually.of_forall (fun x => by simpa only [Real.norm_eq_abs] using h x)
omit [Fintype C] in
omit [DecidableEq D] in

lemma componentFactor_abs_le_term (J : ℕ) (hb : b ∈ Set.Icc (0 : ℝ) 1)
    (c : C) (z : Block label R none → ℕ) (x : Block label R (some c) → ℕ)
    (v : {v : V // color v = c}) :
    |componentFactor label R color s b own J c z x| ≤
      |scoreTerm (s v) b (own v) (fill label R c z x)| := by
  have hterm (u : V) : |scoreTerm (s u) b (own u) (fill label R c z x)| ≤ 1 := by
    simpa only [maskedTerm, maskedFactor, Bool.false_eq_true, ↓reduceIte, scoreTerm]
      using abs_maskedTerm_le_one (s u) hb (own u) (fun _ => false) (fill label R c z x)
  rw [componentFactor, abs_mul, Finset.abs_prod]
  have hp : (∏ u : {v : V // color v = c},
      |scoreTerm (s u) b (own u) (fill label R c z x)|) ≤
      |scoreTerm (s v) b (own v) (fill label R c z x)| := by
    rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ v)]
    have he : (∏ u ∈ Finset.univ.erase v,
        |scoreTerm (s u) b (own u) (fill label R c z x)|) ≤ 1 :=
      Finset.prod_le_one₀ (fun _ _ => abs_nonneg _) (fun u _ => hterm u)
    simpa using mul_le_mul_of_nonneg_right he (abs_nonneg
      (scoreTerm (s v) b (own v) (fill label R c z x)))
  calc
    _ ≤ ∏ u : {v : V // color v = c},
        |scoreTerm (s u) b (own u) (fill label R c z x)| := by
      apply mul_le_of_le_one_left (Finset.prod_nonneg (fun _ _ => abs_nonneg _))
      rw [abs_of_nonneg (blockTrunc_range label R J (some c) x).1]
      exact (blockTrunc_range label R J (some c) x).2
    _ ≤ _ := hp

omit [Fintype C] in

lemma component_integral_abs_le (rate : D → ℝ≥0) (J : ℕ)
    (c : C) (v : {v : V // color v = c}) (z : Block label R none → ℕ)
    (hcompat : ∀ d ∈ s v, label d = none ∨ label d = some c)
    {L lam base a : ℝ} (hL : 0 ≤ L) (ha : 0 ≤ a)
    (hmass : mass (fun d : IntDir label c => rate d) (inside label c (s v)) = L * lam)
    (hlam : a ≤ lam) (hbase : a ≤ base) :
    (∫ x, |componentFactor label R color s (Real.exp (-L * base)) own J c z x|
      ∂batchMeasure (fun i : Block label R (some c) => rate i.1.2)) ≤
        (2 * Real.exp (-L * a)) ^ R := by
  have hb : Real.exp (-L * base) ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨(Real.exp_pos _).le, Real.exp_le_one_iff.mpr (by nlinarith)⟩
  let f := fun w => |maskedTerm (inside label c (s v)) (Real.exp (-L * base))
    (own v) (touched label R c (s v) z) w|
  have he (x : Block label R (some c) → ℕ) :
      |scoreTerm (s v) (Real.exp (-L * base)) (own v) (fill label R c z x)| =
      f (unblockEquiv label R c x) := by
    rw [scoreTerm_eq_masked label R c (s v) _ _ hcompat]
    rfl
  calc
    _ ≤ ∫ x, f (unblockEquiv label R c x)
        ∂batchMeasure (fun i : Block label R (some c) => rate i.1.2) := by
      apply integral_mono
      · apply integrable_block_bounded label R rate (some c)
        intro x
        rw [abs_abs]
        exact componentFactor_bound label R color s _ own J hb c z x
      · apply integrable_block_bounded label R rate (some c)
        intro x
        dsimp only [f]
        rw [abs_abs]
        exact abs_maskedTerm_le_one _ hb _ _ _
      · intro x
        dsimp only
        rw [← he x]
        exact componentFactor_abs_le_term label R color s _ own J hb c z x v
    _ = ∫ w, f w ∂scheduleMeasure (fun d : IntDir label c => rate d) R :=
      (measurePreserving_unblock label R rate c).integral_comp
        (unblockEquiv label R c).measurableEmbedding f
    _ ≤ _ := integral_abs_maskedTerm_exp_le _ _ _ _ hL hmass hlam hbase

end SharpRamseyFive.TupleComponents
end

end OAI
