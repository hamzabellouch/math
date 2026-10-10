import OAI.Combinatorics.BalancedRyser.Construction.Construction
import OAI.Combinatorics.BalancedRyser.Incidence.AffineIncidence
import OAI.Combinatorics.BalancedRyser.Probability.AcyclicProductBound

namespace OAI

open scoped BigOperators Classical

namespace Balanced.LocalFiberBounds

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

theorem line_fiber_card_le_one (S l : Line F) (hne : l ≠ S)
    (x : F → Point F) (hinj : Function.Injective x) (hx : ∀ t, OnLine (x t) S) :
    (Finset.univ.filter (fun t => OnLine (x t) l)).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro t ht u hu
  apply hinj
  exact common_point_eq_of_lines_ne l S hne (x t) (x u)
    (Finset.mem_filter.mp ht).2 (hx t) (Finset.mem_filter.mp hu).2 (hx u)

theorem line_union_fiber_card_le (S : Line F) (L : Finset (Line F))
    (x : F → Point F) (hinj : Function.Injective x) (hx : ∀ t, OnLine (x t) S)
    (hne : ∀ l ∈ L, l ≠ S) :
    (Finset.univ.filter (fun t => ∃ l ∈ L, OnLine (x t) l)).card ≤ L.card := by
  have heq : Finset.univ.filter (fun t => ∃ l ∈ L, OnLine (x t) l) =
      L.biUnion (fun l => Finset.univ.filter (fun t => OnLine (x t) l)) := by
    ext t
    simp
  rw [heq]
  simpa using Finset.card_biUnion_le_card_mul L
    (fun l => Finset.univ.filter (fun t => OnLine (x t) l)) 1
    (fun l hl => line_fiber_card_le_one S l (hne l hl) x hinj hx)

theorem nonTarget_line_union_probability_le (S : Line F) (L : Finset (Line F))
    (x : F → Point F) (hinj : Function.Injective x) (hx : ∀ t, OnLine (x t) S) :
    ((PMF.uniformOfFintype F).toOuterMeasure
      {t | ∃ l ∈ L, l ≠ S ∧ OnLine (x t) l}).toReal ≤
        (L.card : ℝ) / Fintype.card F := by
  rw [DependencyExtraction.uniform_probability_eq_filter_card]
  have heq : Finset.univ.filter (fun t => ∃ l ∈ L, l ≠ S ∧ OnLine (x t) l) =
      Finset.univ.filter (fun t => ∃ l ∈ L.erase S, OnLine (x t) l) := by
    ext t
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase]
    aesop
  rw [heq]
  have hcard := (line_union_fiber_card_le S (L.erase S) x hinj hx
    (fun l hl => (Finset.mem_erase.mp hl).1)).trans (Finset.card_le_card (Finset.erase_subset S L))
  exact div_le_div_of_nonneg_right (by exact_mod_cast hcard) (by positivity)

def indexedThrough (M : MergedPairs F) (U : Finset (Direction F)) (a : Point F) :
    Finset (Direction F × Bool) :=
  Finset.univ.filter (fun ds => ds.1 ∈ U ∧ OnLine a (constituent M ds.1 ds.2))

def partnerCandidates (M : MergedPairs F) (U : Finset (Direction F)) (a : Point F) :
    Finset (Line F) :=
  (indexedThrough M U a).image (fun ds => constituent M ds.1 (!ds.2))

def mergedCandidates (M : MergedPairs F) (U : Finset (Direction F)) (a : Point F) :
    Finset (Line F) :=
  (indexedThrough M U a).biUnion
    (fun ds => {constituent M ds.1 false, constituent M ds.1 true})

theorem card_partnerCandidates_le (M : MergedPairs F) (U : Finset (Direction F))
    (a : Point F) (B : ℕ) (hB : (indexedThrough M U a).card ≤ B) :
    (partnerCandidates M U a).card ≤ B :=
  (Finset.card_image_le).trans hB

theorem card_mergedCandidates_le (M : MergedPairs F) (U : Finset (Direction F))
    (a : Point F) (B : ℕ) (hB : (indexedThrough M U a).card ≤ B) :
    (mergedCandidates M U a).card ≤ 2 * B := by
  have h := Finset.card_biUnion_le_card_mul (indexedThrough M U a)
    (fun ds => {constituent M ds.1 false, constituent M ds.1 true}) 2
    (fun (ds : Direction F × Bool) _ => by
      simpa using (Finset.card_insert_le (constituent M ds.1 false)
        {constituent M ds.1 true}))
  exact h.trans (by omega)

theorem indexedThrough_card_le (M : MergedPairs F) (U : Finset (Direction F))
    (a : Point F) (B : ℕ)
    (hB : (Finset.univ.filter (fun ds : Direction F × Bool =>
      OnLine a (constituent M ds.1 ds.2))).card ≤ B) :
    (indexedThrough M U a).card ≤ B := by
  refine (Finset.card_le_card ?_).trans hB
  intro ds hds
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ ds, (Finset.mem_filter.mp hds).2.2⟩

theorem constituent_mem_mergedCandidates (M : MergedPairs F)
    (U : Finset (Direction F)) (a : Point F) (d : Direction F) (s t : Bool)
    (hd : d ∈ U) (ha : OnLine a (constituent M d s)) :
    constituent M d t ∈ mergedCandidates M U a := by
  refine Finset.mem_biUnion.mpr ⟨(d, s), ?_, ?_⟩
  · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hd, ha⟩
  · cases t <;> simp

theorem partner_mem_partnerCandidates (M : MergedPairs F)
    (U : Finset (Direction F)) (a : Point F) (d : Direction F) (s : Bool)
    (hd : d ∈ U) (ha : OnLine a (constituent M d s)) :
    constituent M d (!s) ∈ partnerCandidates M U a := by
  exact Finset.mem_image.mpr ⟨(d, s),
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, hd, ha⟩, rfl⟩

theorem partner_incidence_probability_le (M : MergedPairs F)
    (U : Finset (Direction F)) (a : Point F) (B : ℕ) (S : Line F)
    (x : F → Point F) (hinj : Function.Injective x) (hx : ∀ t, OnLine (x t) S)
    (hB : (Finset.univ.filter (fun ds : Direction F × Bool =>
      OnLine a (constituent M ds.1 ds.2))).card ≤ B) :
    ((PMF.uniformOfFintype F).toOuterMeasure
      {t | ∃ l ∈ partnerCandidates M U a, l ≠ S ∧ OnLine (x t) l}).toReal ≤
        (B : ℝ) / Fintype.card F := by
  apply (nonTarget_line_union_probability_le S (partnerCandidates M U a) x hinj hx).trans
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact_mod_cast card_partnerCandidates_le M U a B (indexedThrough_card_le M U a B hB)

theorem merged_incidence_probability_le (M : MergedPairs F)
    (U : Finset (Direction F)) (a : Point F) (B : ℕ) (S : Line F)
    (x : F → Point F) (hinj : Function.Injective x) (hx : ∀ t, OnLine (x t) S)
    (hB : (Finset.univ.filter (fun ds : Direction F × Bool =>
      OnLine a (constituent M ds.1 ds.2))).card ≤ B) :
    ((PMF.uniformOfFintype F).toOuterMeasure
      {t | ∃ l ∈ mergedCandidates M U a, l ≠ S ∧ OnLine (x t) l}).toReal ≤
        (2 * (B : ℝ)) / Fintype.card F := by
  apply (nonTarget_line_union_probability_le S (mergedCandidates M U a) x hinj hx).trans
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact_mod_cast card_mergedCandidates_le M U a B (indexedThrough_card_le M U a B hB)

omit [DecidableEq F] in

theorem uniform_probability_mono (E D : F → Prop) (h : ∀ t, E t → D t) :
    ((PMF.uniformOfFintype F).toOuterMeasure {t | E t}).toReal ≤
      ((PMF.uniformOfFintype F).toOuterMeasure {t | D t}).toReal := by
  rw [DependencyExtraction.uniform_probability_eq_filter_card,
    DependencyExtraction.uniform_probability_eq_filter_card]
  apply div_le_div_of_nonneg_right _ (by positivity)
  have hsub : Finset.univ.filter E ⊆ Finset.univ.filter D := by
    intro t ht
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ t, h t (Finset.mem_filter.mp ht).2⟩
  exact_mod_cast Finset.card_le_card hsub

omit [Field F] in
private theorem constituent_ne_of_notMem (M : MergedPairs F) (S : Line F)
    (hS : S ∉ constituentLines M) (d : Direction F) (s : Bool) :
    constituent M d s ≠ S := by
  intro heq
  apply hS
  exact Finset.mem_image.mpr ⟨(d, s), Finset.mem_univ _, heq⟩

theorem partner_specification_probability_le (M : MergedPairs F)
    (U : Finset (Direction F)) (a : Point F) (B : ℕ) (S : Line F)
    (x : F → Point F) (hinj : Function.Injective x) (hx : ∀ t, OnLine (x t) S)
    (hB : (Finset.univ.filter (fun ds : Direction F × Bool =>
      OnLine a (constituent M ds.1 ds.2))).card ≤ B) :
    ((PMF.uniformOfFintype F).toOuterMeasure
      {t | S ∉ constituentLines M ∧ ∃ d ∈ U, ∃ s : Bool,
        OnLine a (constituent M d s) ∧ OnLine (x t) (constituent M d (!s))}).toReal ≤
          (B : ℝ) / Fintype.card F := by
  apply (uniform_probability_mono _ _ ?_).trans
    (partner_incidence_probability_le M U a B S x hinj hx hB)
  rintro t ⟨hS, d, hd, s, ha, ht⟩
  exact ⟨constituent M d (!s), partner_mem_partnerCandidates M U a d s hd ha,
    constituent_ne_of_notMem M S hS d (!s), ht⟩

private theorem mem_mergedPoints_iff_exists (M : MergedPairs F)
    (a : Point F) (d : Direction F) :
    a ∈ mergedPoints M d ↔ ∃ s : Bool, OnLine a (constituent M d s) := by
  simp [mergedPoints, linePoints, Bool.exists_bool]

theorem merged_specification_probability_le (M : MergedPairs F)
    (U : Finset (Direction F)) (a : Point F) (B : ℕ) (S : Line F)
    (x : F → Point F) (hinj : Function.Injective x) (hx : ∀ t, OnLine (x t) S)
    (hB : (Finset.univ.filter (fun ds : Direction F × Bool =>
      OnLine a (constituent M ds.1 ds.2))).card ≤ B) :
    ((PMF.uniformOfFintype F).toOuterMeasure
      {t | S ∉ constituentLines M ∧ ∃ d ∈ U,
        a ∈ mergedPoints M d ∧ x t ∈ mergedPoints M d}).toReal ≤
          (2 * (B : ℝ)) / Fintype.card F := by
  apply (uniform_probability_mono _ _ ?_).trans
    (merged_incidence_probability_le M U a B S x hinj hx hB)
  rintro t ⟨hS, d, hd, ha, ht⟩
  obtain ⟨s, hs⟩ := (mem_mergedPoints_iff_exists M a d).mp ha
  obtain ⟨u, hu⟩ := (mem_mergedPoints_iff_exists M (x t) d).mp ht
  exact ⟨constituent M d u, constituent_mem_mergedCandidates M U a d s u hd hs,
    constituent_ne_of_notMem M S hS d u, hu⟩

end Balanced.LocalFiberBounds

end OAI
