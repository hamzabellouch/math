import Mathlib
import OAI.Combinatorics.IndependentSets.Geometry.PatternInvariant

namespace OAI

namespace LargeIndependentSets

section
open MeasureTheory Set
open Filter
open scoped Topology

noncomputable def extensionLaw {s d n : ℕ} {X : Type*} [LinearOrder X]
    (B : Finset X) (h : B.card = n)
    (μ : ProbabilityMeasure (ListPattern s d (Fin n))) :
    ProbabilityMeasure (ListPattern s d X) :=
  μ.map (ListPattern.extendFin B h)

lemma restriction_extensionLaw {s d n : ℕ} {X : Type*} [LinearOrder X]
    (B : Finset X) (h : B.card = n)
    (μ : ProbabilityMeasure (ListPattern s d (Fin n))) :
    restrictionLaw (B.orderEmbOfFin h) (extensionLaw B h μ) = μ := by
  apply ProbabilityMeasure.toMeasure_injective
  change Measure.map _ (Measure.map _ _) = _
  rw [Measure.map_map (ListPattern.measurable_restrict _) (measurable_of_finite _)]
  have he : ListPattern.restrict (B.orderEmbOfFin h) ∘
      ListPattern.extendFin (s := s) (d := d) B h = id := by
    funext C; exact ListPattern.restrict_extendFin B h C
  rw [he, Measure.map_id]

noncomputable def embeddingInside {n k : ℕ} {X : Type*} [LinearOrder X]
    (B : Finset X) (hB : B.card = k) (e : Fin n ↪o X) (h : ∀ i, e i ∈ B) :
    Fin n ↪o Fin k :=
  ({ toFun := fun i => ⟨e i, h i⟩
     inj' := fun _ _ he => e.injective (congrArg Subtype.val he)
     map_rel_iff' := e.map_rel_iff } : Fin n ↪o B).trans
      (B.orderIsoOfFin hB).symm.toOrderEmbedding

lemma embeddingInside_trans {n k : ℕ} {X : Type*} [LinearOrder X]
    (B : Finset X) (hB : B.card = k) (e : Fin n ↪o X) (h : ∀ i, e i ∈ B) :
    (embeddingInside B hB e h).trans (B.orderEmbOfFin hB) = e := by
  ext i
  change ((B.orderIsoOfFin hB) ((B.orderIsoOfFin hB).symm ⟨e i, h i⟩)).val = e i
  rw [OrderIso.apply_symm_apply]

lemma restriction_extensionLaw_inside {s d n k : ℕ} {X : Type*} [LinearOrder X]
    (B : Finset X) (hB : B.card = k) (e : Fin n ↪o X) (h : ∀ i, e i ∈ B)
    (μ : ProbabilityMeasure (ListPattern s d (Fin k))) :
    restrictionLaw e (extensionLaw B hB μ) =
      restrictionLaw (embeddingInside B hB e h) μ := by
  symm
  calc
    restrictionLaw (embeddingInside B hB e h) μ =
        restrictionLaw (embeddingInside B hB e h)
          (restrictionLaw (B.orderEmbOfFin hB) (extensionLaw B hB μ)) :=
      congrArg _ (restriction_extensionLaw B hB μ).symm
    _ = _ := by rw [restrictionLaw_comp, embeddingInside_trans]

noncomputable def rationalExhaustion (k : ℕ) : Finset ℚ :=
  (Finset.range k).map (Denumerable.eqv ℚ).symm.toEmbedding

lemma rationalExhaustion_card (k : ℕ) : (rationalExhaustion k).card = k := by
  simp [rationalExhaustion]

lemma eventually_mem_rationalExhaustion (x : ℚ) :
    ∀ᶠ k in atTop, x ∈ rationalExhaustion k := by
  filter_upwards [eventually_gt_atTop ((Denumerable.eqv ℚ) x)] with k hk
  apply Finset.mem_map.mpr
  exact ⟨(Denumerable.eqv ℚ) x, Finset.mem_range.mpr hk, Equiv.symm_apply_apply _ _⟩

lemma eventually_range_rationalExhaustion {n : ℕ} (e : Fin n ↪o ℚ) :
    ∀ᶠ k in atTop, ∀ i, e i ∈ rationalExhaustion k :=
  (Filter.eventually_all).mpr (fun i => eventually_mem_rationalExhaustion (e i))

lemma finite_embedding_sorted {n : ℕ} {X : Type*} [LinearOrder X]
    (e : Fin n ↪o X) :
    (Finset.univ.map e.toEmbedding).orderEmbOfFin (by simp) = e := by
  exact (Finset.orderEmbOfFin_unique' (by simp) (fun i =>
    Finset.mem_map.mpr ⟨i, Finset.mem_univ i, rfl⟩)).symm

end

open Filter

noncomputable def tailLarge : ℕ → (Finset ℕ → Prop) → Prop
  | 0, P => P ∅
  | n + 1, P => ∀ᶠ x in (Filter.hyperfilter ℕ : Filter ℕ), tailLarge n (fun S => P (insert x S))

lemma tailLarge_congr {n : ℕ} {P Q : Finset ℕ → Prop}
    (h : ∀ S, P S ↔ Q S) : tailLarge n P ↔ tailLarge n Q := by
  induction n generalizing P Q with
  | zero => exact h ∅
  | succ n ih =>
    simp only [tailLarge]
    apply Filter.eventually_congr
    exact Filter.Eventually.of_forall fun x => ih (fun S => h (insert x S))

lemma tailLarge_color {C : Type*} [Finite C] (c : Finset ℕ → C) (n : ℕ) :
    ∃ a, tailLarge n (fun S => c S = a) := by
  induction n generalizing c with
  | zero => exact ⟨c ∅, rfl⟩
  | succ n ih =>
    have h : ∀ᶠ x in (Filter.hyperfilter ℕ : Filter ℕ),
        ∃ a, tailLarge n (fun S => c (insert x S) = a) :=
      Filter.Eventually.of_forall fun x => ih (fun S => c (insert x S))
    exact (Ultrafilter.eventually_exists_iff).mp h

def RamseyInvariant (n : ℕ) (P : Finset ℕ → Prop) (H : Finset ℕ) : Prop :=
  ∀ S ⊆ H, S.card ≤ n → tailLarge (n - S.card) (fun T => P (S ∪ T))

lemma RamseyInvariant_empty {n : ℕ} {P : Finset ℕ → Prop} (h : tailLarge n P) :
    RamseyInvariant n P ∅ := by
  intro S hS _
  have : S = ∅ := Finset.subset_empty.mp hS
  subst S
  simpa [tailLarge] using h

lemma RamseyInvariant_extend {n : ℕ} {P : Finset ℕ → Prop} {H : Finset ℕ}
    (hH : RamseyInvariant n P H) :
    ∃ x ∉ H, RamseyInvariant n P (insert x H) := by
  classical
  have hg : ∀ᶠ x in (Filter.hyperfilter ℕ : Filter ℕ),
      ∀ S ∈ H.powerset, S.card < n →
        tailLarge (n - (S.card + 1)) (fun T => P (insert x S ∪ T)) := by
    apply (Filter.eventually_all_finset H.powerset).mpr
    intro S hS
    by_cases hs : S.card < n
    · have h := hH S (Finset.mem_powerset.mp hS) hs.le
      have he : n - S.card = (n - (S.card + 1)) + 1 := by omega
      rw [he, tailLarge] at h
      filter_upwards [h] with x hx _
      apply (tailLarge_congr (fun T => ?_)).mp hx
      have heq : S ∪ insert x T = insert x S ∪ T := by
        ext y
        simp only [Finset.mem_union, Finset.mem_insert]
        tauto
      rw [heq]
    · exact Filter.Eventually.of_forall fun _ => fun hs' => (hs hs').elim
  have hf : ∀ᶠ x in (Filter.hyperfilter ℕ : Filter ℕ), x ∉ H := by
    have hbound : ∀ᶠ x : ℕ in atTop, H.sup id < x := eventually_gt_atTop _
    have hbound' := Nat.hyperfilter_le_atTop hbound
    filter_upwards [hbound'] with x hx hmem
    exact (not_lt_of_ge (Finset.le_sup (f := id) hmem)) hx
  obtain ⟨x, hx, hgx⟩ := (hf.and hg).exists
  refine ⟨x, hx, ?_⟩
  intro S hS hn
  by_cases hxS : x ∈ S
  · have he : insert x (S.erase x) = S := Finset.insert_erase hxS
    have hsub : S.erase x ⊆ H := by
      intro y hy
      rcases Finset.mem_erase.mp hy with ⟨hne, hyS⟩
      exact (Finset.mem_insert.mp (hS hyS)).resolve_left hne
    have hc : (S.erase x).card + 1 = S.card := Finset.card_erase_add_one hxS
    have hlt : (S.erase x).card < n := by omega
    have h := hgx (S.erase x) (Finset.mem_powerset.mpr hsub) hlt
    simpa only [hc, he] using h
  · exact hH S (by
      intro y hy
      rcases Finset.mem_insert.mp (hS hy) with h | h
      · subst y; exact (hxS hy).elim
      · exact h) hn

lemma tailLarge_homogeneous {n : ℕ} {P : Finset ℕ → Prop}
    (h : tailLarge n P) (k : ℕ) :
    ∃ H : Finset ℕ, H.card = k ∧ ∀ S ⊆ H, S.card = n → P S := by
  have haux : ∀ j, ∃ H : Finset ℕ, H.card = j ∧ RamseyInvariant n P H := by
    intro j
    induction j with
    | zero => exact ⟨∅, rfl, RamseyInvariant_empty h⟩
    | succ j ih =>
      obtain ⟨H, hc, hH⟩ := ih
      obtain ⟨x, hx, hnew⟩ := RamseyInvariant_extend hH
      exact ⟨insert x H, by simp [Finset.card_insert_of_notMem hx, hc], hnew⟩
  obtain ⟨H, hc, hH⟩ := haux k
  refine ⟨H, hc, ?_⟩
  intro S hS hn
  have h := hH S hS hn.le
  simpa [hn, tailLarge] using h

theorem finite_homogeneous_of_infinite {C : Type*} [Finite C]
    (c : Finset ℕ → C) (n k : ℕ) :
    ∃ H : Finset ℕ, H.card = k ∧ ∃ a, ∀ S ⊆ H, S.card = n → c S = a := by
  obtain ⟨a, ha⟩ := tailLarge_color c n
  obtain ⟨H, hc, hH⟩ := tailLarge_homogeneous ha k
  exact ⟨H, hc, a, hH⟩

theorem finite_hypergraph_ramsey (colors n k : ℕ) :
    ∃ r ≥ k, ∀ c : Finset ℕ → Fin colors,
      ∃ H : Finset ℕ, H ⊆ Finset.range r ∧ H.card = k ∧
        ∃ a, ∀ S ⊆ H, S.card = n → c S = a := by
  classical
  let U (H : {H : Finset ℕ // H.card = k}) : Set (Finset ℕ → Fin colors) :=
    {c | ∃ a, ∀ S ∈ H.val.powerset.filter (fun S => S.card = n), c S = a}
  have hU : ∀ H, IsOpen (U H) := by
    intro H
    change IsOpen {c : Finset ℕ → Fin colors | ∃ a, ∀ S ∈ H.val.powerset.filter (fun S => S.card = n), c S = a}
    simp only [Set.ofPred_exists, Set.ofPred_forall]
    apply isOpen_iUnion
    intro a
    apply isOpen_biInter_finset
    intro S _
    change IsOpen ((fun c : Finset ℕ → Fin colors => c S) ⁻¹' {a})
    exact (isOpen_discrete ({a} : Set (Fin colors))).preimage
      (continuous_apply S : Continuous (fun c : Finset ℕ → Fin colors => c S))
  have hcover : (Set.univ : Set (Finset ℕ → Fin colors)) ⊆ ⋃ H, U H := by
    intro c _
    obtain ⟨H, hc, a, hH⟩ := finite_homogeneous_of_infinite c n k
    apply Set.mem_iUnion.mpr
    refine ⟨⟨H, hc⟩, a, ?_⟩
    intro S hS
    obtain ⟨hsub, hcard⟩ := Finset.mem_filter.mp hS
    exact hH S (Finset.mem_powerset.mp hsub) hcard
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover U hU hcover
  let bound := (t.biUnion fun H => H.val).sup id + 1
  refine ⟨max bound k, le_max_right _ _, ?_⟩
  intro c
  obtain ⟨H, hH, hc⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ c))
  refine ⟨H.val, ?_, H.property, ?_⟩
  · intro x hx
    apply Finset.mem_range.mpr
    have hx' : x ∈ t.biUnion (fun H => H.val) := Finset.mem_biUnion.mpr ⟨H, hH, hx⟩
    have hle := Finset.le_sup (f := id) hx'
    exact lt_of_lt_of_le (Nat.lt_succ_of_le hle) (le_max_left _ _)
  · obtain ⟨a, ha⟩ := hc
    exact ⟨a, fun S hS hn => ha S (Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hS, hn⟩)⟩

theorem finite_hypergraph_ramsey_subset (colors n k : ℕ) :
    ∃ r ≥ k, ∀ H : Finset ℕ, r ≤ H.card → ∀ c : Finset ℕ → Fin colors,
      ∃ K ⊆ H, K.card = k ∧ ∃ a, ∀ S ⊆ K, S.card = n → c S = a := by
  classical
  obtain ⟨r, hr, hram⟩ := finite_hypergraph_ramsey colors n k
  refine ⟨r, hr, ?_⟩
  intro H hH c
  obtain ⟨J, hJH, hJ⟩ := Finset.exists_subset_card_eq hH
  let e := J.orderEmbOfFin hJ
  let f : ℕ → ℕ := fun x => if hx : x < r then e ⟨x, hx⟩ else 0
  have hf : Set.InjOn f (↑(Finset.range r) : Set ℕ) := by
    intro x hx y hy hxy
    simp only [Finset.mem_coe, Finset.mem_range] at hx hy
    have h := e.injective (by simpa only [f, dite_eq_left hx, dite_eq_left hy] using hxy)
    exact congrArg Fin.val h
  obtain ⟨K, hK, hcard, a, ha⟩ := hram (fun S => c (S.image f))
  have hfK : Set.InjOn f (↑K : Set ℕ) := hf.mono hK
  refine ⟨K.image f, ?_, (Finset.card_image_of_injOn hfK).trans hcard, a, ?_⟩
  · intro y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    have hx' := Finset.mem_range.mp (hK hx)
    apply hJH
    simpa only [f, dite_eq_left hx'] using J.orderEmbOfFin_mem hJ ⟨x, hx'⟩
  · intro S hS hn
    let T := K.filter (fun x => f x ∈ S)
    have hTK : T ⊆ K := Finset.filter_subset _ _
    have himage : T.image f = S := by
      ext y
      constructor
      · intro hy
        obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
        exact (Finset.mem_filter.mp hx).2
      · intro hy
        obtain ⟨x, hx, hxy⟩ := Finset.mem_image.mp (hS hy)
        apply Finset.mem_image.mpr
        exact ⟨x, Finset.mem_filter.mpr ⟨hx, hxy ▸ hy⟩, hxy⟩
    have hTcard : T.card = n := by
      rw [← Finset.card_image_of_injOn (hfK.mono hTK), himage, hn]
    simpa only [himage] using ha T hTK hTcard

theorem finite_simultaneous_ramsey (colors : ℕ → ℕ) (m k : ℕ) :
    ∃ r ≥ k, ∀ H : Finset ℕ, r ≤ H.card →
      ∀ c : (n : ℕ) → Finset ℕ → Fin (colors n),
      ∃ K ⊆ H, K.card = k ∧ ∀ n < m, ∃ a,
        ∀ S ⊆ K, S.card = n → c n S = a := by
  classical
  induction m generalizing k with
  | zero =>
    refine ⟨k, le_rfl, ?_⟩
    intro H hH c
    obtain ⟨K, hKH, hK⟩ := Finset.exists_subset_card_eq hH
    exact ⟨K, hKH, hK, by omega⟩
  | succ m ih =>
    obtain ⟨r₀, hr₀, hrec⟩ := ih k
    obtain ⟨r, hr, hlast⟩ := finite_hypergraph_ramsey_subset (colors m) m r₀
    refine ⟨r, hr₀.trans hr, ?_⟩
    intro H hH c
    obtain ⟨J, hJH, hJcard, a, ha⟩ := hlast H hH (c m)
    obtain ⟨K, hKJ, hKcard, hK⟩ := hrec J hJcard.ge c
    refine ⟨K, hKJ.trans hJH, hKcard, ?_⟩
    intro n hn
    by_cases hnm : n < m
    · exact hK n hnm
    · have he : n = m := by omega
      subst n
      exact ⟨a, fun S hS hScard => ha S (hS.trans hKJ) hScard⟩

theorem compact_simultaneous_ramsey (X : ℕ → Type*)
    [∀ n, PseudoMetricSpace (X n)] [∀ n, CompactSpace (X n)]
    (m k : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ r ≥ k, ∀ H : Finset ℕ, r ≤ H.card →
      ∀ f : (n : ℕ) → Finset ℕ → X n,
      ∃ K ⊆ H, K.card = k ∧ ∀ n < m,
        ∀ S ⊆ K, S.card = n → ∀ T ⊆ K, T.card = n →
          dist (f n S) (f n T) < ε := by
  classical
  have hcover (n : ℕ) : ∃ t : Finset (X n),
      ∀ x : X n, ∃ y ∈ t, dist x y < ε / 2 := by
    obtain ⟨t, _, htfin, ht⟩ := finite_cover_balls_of_compact
      (isCompact_univ : IsCompact (Set.univ : Set (X n))) (half_pos hε)
    refine ⟨htfin.toFinset, ?_⟩
    intro x
    obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ x))
    exact ⟨y, htfin.mem_toFinset.mpr hy, hxy⟩
  choose t ht using hcover
  obtain ⟨r, hr, hram⟩ := finite_simultaneous_ramsey (fun n => (t n).card) m k
  refine ⟨r, hr, ?_⟩
  intro H hH f
  have hchoice (n : ℕ) (S : Finset ℕ) :
      ∃ c : Fin (t n).card,
        dist (f n S) ((t n).equivFin.symm c).val < ε / 2 := by
    obtain ⟨y, hy, hdist⟩ := ht n (f n S)
    exact ⟨(t n).equivFin ⟨y, hy⟩, by simpa using hdist⟩
  choose c hc using hchoice
  obtain ⟨K, hKH, hK, hhom⟩ := hram H hH c
  refine ⟨K, hKH, hK, ?_⟩
  intro n hn S hSK hS T hTK hT
  obtain ⟨a, ha⟩ := hhom n hn
  have hs := hc n S
  have ht := hc n T
  rw [ha S hSK hS] at hs
  rw [ha T hTK hT] at ht
  calc
    dist (f n S) (f n T) ≤
      dist (f n S) ((t n).equivFin.symm a).val +
      dist (f n T) ((t n).equivFin.symm a).val := dist_triangle_right _ _ _
    _ < ε / 2 + ε / 2 := add_lt_add hs ht
    _ = ε := add_halves ε

end LargeIndependentSets

end OAI
