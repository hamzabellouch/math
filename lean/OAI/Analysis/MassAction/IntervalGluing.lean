import Mathlib

namespace OAI

universe uAlpha uBeta

/-! Elementary interval-gluing facts for the affine-label construction. -/
namespace Problem326.IntervalGluing

/-- Removing nonmaximal members of a finite family preserves its union. -/
theorem exists_maximal_subfamily {α : Type uAlpha} {β : Type uBeta} (S : Finset α) (U : α → Set β) :
    ∃ T : Finset α, T ⊆ S ∧
      (∀ x ∈ S, ∃ y ∈ T, U x ⊆ U y) ∧
      (∀ x ∈ T, ∀ y ∈ T, U x ⊆ U y → U y ⊆ U x) := by
  classical
  let T := S.filter (fun x => MaximalFor (· ∈ S) U x)
  refine ⟨T, Finset.filter_subset _ _, ?_, ?_⟩
  · intro x hx
    obtain ⟨V, hxV, hV⟩ := (S.image U).exists_le_maximal (Finset.mem_image.mpr ⟨x, hx, rfl⟩)
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hV.1
    refine ⟨y, Finset.mem_filter.mpr ⟨hy, hy, ?_⟩, hxV⟩
    intro z hz hyz
    exact hV.2 (Finset.mem_image.mpr ⟨z, hz, rfl⟩) hyz
  · intro x hx y hy hxy
    have hmax := (Finset.mem_filter.mp hx).2
    exact hmax.2 (Finset.mem_filter.mp hy).1 hxy

/-- For centered intervals, noncontainment forces both endpoints to follow the
order of the centers. -/
theorem endpoints_order_of_noncontainment {t u r s : ℝ}
    (htu : t < u)
    (hntu : ¬ Set.Ioo (t-r) (t+r) ⊆ Set.Ioo (u-s) (u+s))
    (hnut : ¬ Set.Ioo (u-s) (u+s) ⊆ Set.Ioo (t-r) (t+r)) :
    t-r < u-s ∧ t+r < u+s := by
  constructor
  · by_contra h
    apply hntu
    apply Set.Ioo_subset_Ioo
    · exact le_of_not_gt h
    · linarith
  · by_contra h
    apply hnut
    apply Set.Ioo_subset_Ioo
    · linarith
    · exact le_of_not_gt h

/-- Two nonempty centered intervals with mutual inclusion have equal centers. -/
theorem center_eq_of_mutual_subset {t u r s : ℝ} (hr : 0 < r) (hs : 0 < s)
    (h₁ : Set.Ioo (t-r) (t+r) ⊆ Set.Ioo (u-s) (u+s))
    (h₂ : Set.Ioo (u-s) (u+s) ⊆ Set.Ioo (t-r) (t+r)) : t = u := by
  have h₁' := (Set.Ioo_subset_Ioo_iff (show t-r < t+r by linarith)).mp h₁
  have h₂' := (Set.Ioo_subset_Ioo_iff (show u-s < u+s by linarith)).mp h₂
  linarith

/-- An arbitrary positive radius function on a compact interval has a finite
centered subcover whose centers and both endpoint lists are strictly ordered.
No continuity of the radius function is required. -/
theorem exists_ordered_interval_cover {a b : ℝ} (hab : a ≤ b)
    (r : ℝ → ℝ) (hr : ∀ t ∈ Set.Icc a b, 0 < r t) :
    ∃ n : ℕ, ∃ t : Fin (n+1) → ℝ,
      StrictMono t ∧ (∀ i, t i ∈ Set.Icc a b) ∧
      StrictMono (fun i => t i - r (t i)) ∧
      StrictMono (fun i => t i + r (t i)) ∧
      (∀ x ∈ Set.Icc a b, ∃ i, x ∈ Set.Ioo (t i-r (t i)) (t i+r (t i))) := by
  classical
  let U : ℝ → Set ℝ := fun t => Set.Ioo (t-r t) (t+r t)
  have hcov : Set.Icc a b ⊆ ⋃ t ∈ Set.Icc a b, U t := by
    intro x hx
    refine Set.mem_iUnion.mpr ⟨x, Set.mem_iUnion.mpr ⟨hx, ?_⟩⟩
    have := hr x hx
    exact ⟨by linarith, by linarith⟩
  obtain ⟨S', hS', hSf, hcovS⟩ :=
    isCompact_Icc.elim_finite_subcover_image (fun _ _ => isOpen_Ioo) hcov
  let S := hSf.toFinset
  obtain ⟨T, hTS, hdom, hmax⟩ := exists_maximal_subfamily S U
  have hTmem : ∀ t ∈ T, t ∈ Set.Icc a b := by
    intro t ht
    exact hS' (by simpa [S] using hTS ht)
  have hTcov : ∀ x ∈ Set.Icc a b, ∃ t ∈ T, x ∈ U t := by
    intro x hx
    obtain ⟨u, hu, hxu⟩ := Set.mem_iUnion₂.mp (hcovS hx)
    obtain ⟨t, ht, hut⟩ := hdom u (by simpa [S] using hu)
    exact ⟨t, ht, hut hxu⟩
  have hTne : T.Nonempty := by
    obtain ⟨t, ht, _⟩ := hTcov a ⟨le_rfl, hab⟩
    exact ⟨t, ht⟩
  obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero (ne_of_gt hTne.card_pos)
  let t : Fin (n+1) ↪o ℝ := T.orderEmbOfFin hn
  have htmem : ∀ i, t i ∈ T := T.orderEmbOfFin_mem hn
  have htnot : ∀ i j, i < j → ¬ U (t i) ⊆ U (t j) := by
    intro i j hij hsub
    have heq := center_eq_of_mutual_subset
      (hr _ (hTmem _ (htmem i))) (hr _ (hTmem _ (htmem j)))
      hsub (hmax _ (htmem i) _ (htmem j) hsub)
    exact (ne_of_lt (t.strictMono hij)) heq
  have htends : ∀ i j, i < j →
      t i-r (t i) < t j-r (t j) ∧ t i+r (t i) < t j+r (t j) := by
    intro i j hij
    apply endpoints_order_of_noncontainment (t.strictMono hij) (htnot i j hij)
    intro hsub
    exact htnot i j hij (hmax _ (htmem j) _ (htmem i) hsub)
  refine ⟨n, t, t.strictMono, (fun i => hTmem _ (htmem i)),
    (fun _ _ hij => (htends _ _ hij).1),
    (fun _ _ hij => (htends _ _ hij).2), ?_⟩
  intro x hx
  obtain ⟨u, hu, hxu⟩ := hTcov x hx
  have hurange : u ∈ Set.range t := by
    rw [show Set.range t = (T : Set ℝ) from T.range_orderEmbOfFin hn]
    exact hu
  obtain ⟨i, rfl⟩ := hurange
  exact ⟨i, hxu⟩

/-- Overlapping intervals with ordered centers admit a transition cut inside both
intervals and strictly between their centers. -/
theorem exists_overlap_cut {t u L R L' R' : ℝ}
    (htu : t < u) (hLt : L < t) (htR : t < R)
    (hLu : L' < u) (huR : u < R') (hoverlap : L' < R) :
    ∃ q : ℝ, t < q ∧ q < u ∧ q ∈ Set.Ioo L R ∧ q ∈ Set.Ioo L' R' := by
  have hgap : max t L' < min u R := by
    exact max_lt (lt_min htu htR) (lt_min hLu hoverlap)
  obtain ⟨q, hqlo, hqhi⟩ := exists_between hgap
  have htq : t < q := lt_of_le_of_lt (le_max_left _ _) hqlo
  have hLq : L' < q := lt_of_le_of_lt (le_max_right _ _) hqlo
  have hqu : q < u := lt_of_lt_of_le hqhi (min_le_left _ _)
  have hqR : q < R := lt_of_lt_of_le hqhi (min_le_right _ _)
  exact ⟨q, htq, hqu, ⟨hLt.trans htq, hqR⟩, ⟨hLq, hqu.trans huR⟩⟩

/-- In an ordered interval cover, neighboring intervals overlap. Ordering both
endpoints is the property obtained by deleting contained intervals. -/
theorem consecutive_overlap {n : ℕ} {a b : ℝ}
    (t L R : Fin (n + 1) → ℝ)
    (hL : StrictMono L) (hR : StrictMono R)
    (hcenter : ∀ j, L j < t j ∧ t j < R j)
    (hcenter_mem : ∀ j, t j ∈ Set.Icc a b)
    (hcover : ∀ x ∈ Set.Icc a b, ∃ j, x ∈ Set.Ioo (L j) (R j))
    (i : Fin n) : L i.succ < R i.castSucc := by
  by_contra h
  have hgap : R i.castSucc ≤ L i.succ := le_of_not_gt h
  have hx : R i.castSucc ∈ Set.Icc a b := by
    constructor
    · exact (hcenter_mem i.castSucc).1.trans (hcenter i.castSucc).2.le
    · exact hgap.trans ((hcenter i.succ).1.le.trans (hcenter_mem i.succ).2)
  obtain ⟨j, hjL, hjR⟩ := hcover (R i.castSucc) hx
  by_cases hji : j ≤ i.castSucc
  · exact (not_lt_of_ge (hR.monotone hji)) hjR
  · have hij : i.succ ≤ j := by
      change i.val + 1 ≤ j.val
      have : i.castSucc < j := lt_of_not_ge hji
      change i.val < j.val at this
      omega
    exact (not_lt_of_ge (hgap.trans (hL.monotone hij))) hjL

/-- A simultaneous choice of all transition cuts in an ordered interval cover. -/
theorem exists_consecutive_cuts {n : ℕ} {a b : ℝ}
    (t L R : Fin (n + 1) → ℝ)
    (ht : StrictMono t) (hL : StrictMono L) (hR : StrictMono R)
    (hcenter : ∀ j, L j < t j ∧ t j < R j)
    (hcenter_mem : ∀ j, t j ∈ Set.Icc a b)
    (hcover : ∀ x ∈ Set.Icc a b, ∃ j, x ∈ Set.Ioo (L j) (R j)) :
    ∃ q : Fin n → ℝ, ∀ i,
      t i.castSucc < q i ∧ q i < t i.succ ∧
      q i ∈ Set.Ioo (L i.castSucc) (R i.castSucc) ∧
      q i ∈ Set.Ioo (L i.succ) (R i.succ) := by
  have hex : ∀ i : Fin n, ∃ q : ℝ,
      t i.castSucc < q ∧ q < t i.succ ∧
      q ∈ Set.Ioo (L i.castSucc) (R i.castSucc) ∧
      q ∈ Set.Ioo (L i.succ) (R i.succ) := by
    intro i
    apply exists_overlap_cut (ht (by simp))
      (hcenter i.castSucc).1 (hcenter i.castSucc).2
      (hcenter i.succ).1 (hcenter i.succ).2
    exact consecutive_overlap t L R hL hR hcenter hcenter_mem hcover i
  exact Classical.axiomOfChoice hex

/-- In an ordered centered cover, the first and last intervals contain the
corresponding endpoints of the covered compact interval. -/
theorem endpoint_membership {n : ℕ} {a b : ℝ} (hab : a ≤ b)
    (t L R : Fin (n+1) → ℝ) (hL : StrictMono L) (hR : StrictMono R)
    (hcenter : ∀ j, L j < t j ∧ t j < R j)
    (hcenter_mem : ∀ j, t j ∈ Set.Icc a b)
    (hcover : ∀ x ∈ Set.Icc a b, ∃ j, x ∈ Set.Ioo (L j) (R j)) :
    a ∈ Set.Ioo (L 0) (R 0) ∧
    b ∈ Set.Ioo (L (Fin.last n)) (R (Fin.last n)) := by
  obtain ⟨i, hi⟩ := hcover a ⟨le_rfl, hab⟩
  obtain ⟨j, hj⟩ := hcover b ⟨hab, le_rfl⟩
  constructor
  · exact ⟨(hL.monotone (Fin.zero_le i)).trans_lt hi.1,
      (hcenter_mem 0).1.trans_lt (hcenter 0).2⟩
  · exact ⟨(hcenter (Fin.last n)).1.trans_le (hcenter_mem (Fin.last n)).2,
      hj.2.trans_le (hR.monotone (Fin.le_last j))⟩

/-- Finite interval gluing data for an arbitrary positive radius function.
The chosen transition cuts lie in both adjacent intervals and strictly between
adjacent centers. Together with endpoint membership this covers every closed
piece between successive cuts by its designated interval. -/
theorem exists_interval_gluing {a b : ℝ} (hab : a ≤ b)
    (r : ℝ → ℝ) (hr : ∀ t ∈ Set.Icc a b, 0 < r t) :
    ∃ n : ℕ, ∃ t : Fin (n+1) → ℝ, ∃ q : Fin n → ℝ,
      StrictMono t ∧ (∀ i, t i ∈ Set.Icc a b) ∧
      (a ∈ Set.Ioo (t 0-r (t 0)) (t 0+r (t 0))) ∧
      (b ∈ Set.Ioo (t (Fin.last n)-r (t (Fin.last n)))
        (t (Fin.last n)+r (t (Fin.last n)))) ∧
      (∀ i, t i.castSucc < q i ∧ q i < t i.succ ∧
        q i ∈ Set.Ioo (t i.castSucc-r (t i.castSucc))
          (t i.castSucc+r (t i.castSucc)) ∧
        q i ∈ Set.Ioo (t i.succ-r (t i.succ)) (t i.succ+r (t i.succ))) := by
  obtain ⟨n, t, ht, htm, hL, hR, hcover⟩ := exists_ordered_interval_cover hab r hr
  have hcenter : ∀ i, t i-r (t i) < t i ∧ t i < t i+r (t i) := by
    intro i
    have := hr (t i) (htm i)
    constructor <;> linarith
  obtain ⟨q, hq⟩ := exists_consecutive_cuts t
    (fun i => t i-r (t i)) (fun i => t i+r (t i)) ht hL hR hcenter htm hcover
  have he := endpoint_membership hab t
    (fun i => t i-r (t i)) (fun i => t i+r (t i)) hL hR hcenter htm hcover
  exact ⟨n, t, q, ht, htm, he.1, he.2, hq⟩

end Problem326.IntervalGluing

end OAI
