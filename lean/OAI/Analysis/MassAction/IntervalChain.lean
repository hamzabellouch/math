import Mathlib

namespace OAI

universe uIota uX

noncomputable section

namespace Problem326.IntervalChain

/-- A finite cover can be reduced so that no selected set is contained in
another selected set. -/
theorem exists_irredundant_subcover {ι : Type uIota} {X : Type uX}
    (s : Finset ι) (U : ι → Set X) (K : Set X)
    (hcover : ∀ x ∈ K, ∃ i ∈ s, x ∈ U i) :
    ∃ t : Finset ι, t ⊆ s ∧
      (∀ x ∈ K, ∃ i ∈ t, x ∈ U i) ∧
      ∀ i ∈ t, ∀ j ∈ t, i ≠ j → ¬ U i ⊆ U j := by
  classical
  let P : Finset ι → Prop := fun t => t ⊆ s ∧ ∀ x ∈ K, ∃ i ∈ t, x ∈ U i
  obtain ⟨t, ht⟩ := exists_minimalFor_of_wellFoundedLT P Finset.card ⟨s, ⟨by rfl, hcover⟩⟩
  refine ⟨t, ht.prop.1, ht.prop.2, ?_⟩
  intro i hi j hj hij hsub
  have herase : P (t.erase i) := by
    refine ⟨(Finset.erase_subset i t).trans ht.prop.1, ?_⟩
    intro x hx
    obtain ⟨k, hk, hxk⟩ := ht.prop.2 x hx
    by_cases hki : k = i
    · subst k
      exact ⟨j, Finset.mem_erase.mpr ⟨Ne.symm hij, hj⟩, hsub hxk⟩
    · exact ⟨k, Finset.mem_erase.mpr ⟨hki, hk⟩, hxk⟩
  exact ht.not_lt herase (Finset.card_erase_lt_of_mem hi)

/-- Compactness supplies finitely many centers from the original interval. -/
theorem exists_finite_center_cover {a b : ℝ} (ρ : ℝ → ℝ)
    (hρ : ∀ t ∈ Set.Icc a b, 0 < ρ t) :
    ∃ s : Finset ℝ,
      (∀ t ∈ s, t ∈ Set.Icc a b) ∧
      ∀ x ∈ Set.Icc a b, ∃ t ∈ s, x ∈ Set.Ioo (t - ρ t) (t + ρ t) := by
  classical
  have hcover : Set.Icc a b ⊆
      ⋃ t ∈ Set.Icc a b, Set.Ioo (t - ρ t) (t + ρ t) := by
    intro x hx
    refine Set.mem_iUnion.mpr ⟨x, Set.mem_iUnion.mpr ⟨hx, ?_⟩⟩
    have hp := hρ x hx
    exact ⟨by linarith, by linarith⟩
  obtain ⟨s, hs, hfin, hcov⟩ := isCompact_Icc.elim_finite_subcover_image
    (fun t ht => isOpen_Ioo) hcover
  refine ⟨hfin.toFinset, ?_, ?_⟩
  · intro t ht
    exact hs (hfin.mem_toFinset.mp ht)
  · intro x hx
    obtain ⟨t, ht, hxt⟩ := Set.mem_iUnion₂.mp (hcov hx)
    exact ⟨t, hfin.mem_toFinset.mpr ht, hxt⟩

/-- Noncontainment forces the interval endpoints to be ordered in the same
way as their centers. -/
theorem endpoints_strictMono {u v ru rv : ℝ}
    (huv : u < v)
    (hnot : ¬ Set.Ioo (u - ru) (u + ru) ⊆ Set.Ioo (v - rv) (v + rv))
    (hnot' : ¬ Set.Ioo (v - rv) (v + rv) ⊆ Set.Ioo (u - ru) (u + ru)) :
    u - ru < v - rv ∧ u + ru < v + rv := by
  constructor
  · by_contra h
    have hl : v - rv ≤ u - ru := le_of_not_gt h
    apply hnot
    intro x hx
    exact ⟨lt_of_le_of_lt hl hx.1, by linarith [hx.2]⟩
  · by_contra h
    have hr : v + rv ≤ u + ru := le_of_not_gt h
    apply hnot'
    intro x hx
    exact ⟨by linarith [hx.1], lt_of_lt_of_le hx.2 hr⟩

/-- Successive selected intervals overlap when their union covers the
whole interval and their endpoint order follows their center order. -/
theorem adjacent_overlap {a b : ℝ} {ρ : ℝ → ℝ} {s : Finset ℝ}
    (hcenters : ∀ t ∈ s, t ∈ Set.Icc a b)
    (hρ : ∀ t ∈ s, 0 < ρ t)
    (hcover : ∀ x ∈ Set.Icc a b, ∃ t ∈ s, x ∈ Set.Ioo (t - ρ t) (t + ρ t))
    (horder : ∀ u ∈ s, ∀ v ∈ s, u < v →
      u - ρ u < v - ρ v ∧ u + ρ u < v + ρ v)
    {u v : ℝ} (hu : u ∈ s) (hv : v ∈ s) (huv : u < v)
    (hadj : ∀ w ∈ s, u < w → v ≤ w) :
    v - ρ v < u + ρ u := by
  by_contra h
  have hgap : u + ρ u ≤ v - ρ v := le_of_not_gt h
  have hx : u + ρ u ∈ Set.Icc a b := by
    have hu' := hcenters u hu
    have hv' := hcenters v hv
    have hru := hρ u hu
    have hrv := hρ v hv
    constructor <;> linarith [hu'.1, hv'.2]
  obtain ⟨w, hw, hxw⟩ := hcover (u + ρ u) hx
  rcases lt_trichotomy w u with hwu | rfl | huw
  · have hord := (horder w hw u hu hwu).2
    linarith [hxw.2]
  · exact (lt_irrefl _ hxw.2)
  · have hvw := hadj w hw huw
    rcases hvw.eq_or_lt with rfl | hvw
    · linarith [hxw.1]
    · have hord := (horder v hv w hw hvw).1
      linarith [hxw.1]

/-- An overlapping pair admits a transition cut in both neighborhoods and
strictly between the two centers. -/
theorem exists_transition_cut {u v ru rv : ℝ}
    (huv : u < v) (hru : 0 < ru) (hrv : 0 < rv)
    (hoverlap : v - rv < u + ru) :
    ∃ q : ℝ, u < q ∧ q < v ∧
      q ∈ Set.Ioo (u - ru) (u + ru) ∧
      q ∈ Set.Ioo (v - rv) (v + rv) := by
  have h : max u (v - rv) < min v (u + ru) := by
    apply max_lt
    · exact lt_min huv (by linarith)
    · exact lt_min (by linarith) hoverlap
  obtain ⟨q, hlo, hhi⟩ := exists_between h
  have huq : u < q := lt_of_le_of_lt (le_max_left _ _) hlo
  have hvq : v - rv < q := lt_of_le_of_lt (le_max_right _ _) hlo
  have hqv : q < v := lt_of_lt_of_le hhi (min_le_left _ _)
  have hqu : q < u + ru := lt_of_lt_of_le hhi (min_le_right _ _)
  exact ⟨q, huq, hqv, ⟨by linarith, hqu⟩, ⟨hvq, by linarith⟩⟩

/-- The first selected neighborhood contains the left endpoint. -/
theorem left_endpoint_mem {a b : ℝ} {ρ : ℝ → ℝ} {s : Finset ℝ}
    (hab : a ≤ b)
    (hcenters : ∀ t ∈ s, t ∈ Set.Icc a b)
    (hρ : ∀ t ∈ s, 0 < ρ t)
    (hcover : ∀ x ∈ Set.Icc a b, ∃ t ∈ s, x ∈ Set.Ioo (t - ρ t) (t + ρ t))
    (horder : ∀ u ∈ s, ∀ v ∈ s, u < v →
      u - ρ u < v - ρ v ∧ u + ρ u < v + ρ v)
    {u : ℝ} (hu : u ∈ s) (hmin : ∀ w ∈ s, u ≤ w) :
    a ∈ Set.Ioo (u - ρ u) (u + ρ u) := by
  obtain ⟨w, hw, haw⟩ := hcover a ⟨le_rfl, hab⟩
  have hru := hρ u hu
  have hau := (hcenters u hu).1
  constructor
  · rcases (hmin w hw).eq_or_lt with rfl | huw
    · exact haw.1
    · exact ((horder u hu w hw huw).1).trans haw.1
  · linarith

/-- The last selected neighborhood contains the right endpoint. -/
theorem right_endpoint_mem {a b : ℝ} {ρ : ℝ → ℝ} {s : Finset ℝ}
    (hab : a ≤ b)
    (hcenters : ∀ t ∈ s, t ∈ Set.Icc a b)
    (hρ : ∀ t ∈ s, 0 < ρ t)
    (hcover : ∀ x ∈ Set.Icc a b, ∃ t ∈ s, x ∈ Set.Ioo (t - ρ t) (t + ρ t))
    (horder : ∀ u ∈ s, ∀ v ∈ s, u < v →
      u - ρ u < v - ρ v ∧ u + ρ u < v + ρ v)
    {v : ℝ} (hv : v ∈ s) (hmax : ∀ w ∈ s, w ≤ v) :
    b ∈ Set.Ioo (v - ρ v) (v + ρ v) := by
  obtain ⟨w, hw, hbw⟩ := hcover b ⟨hab, le_rfl⟩
  have hrv := hρ v hv
  have hvb := (hcenters v hv).2
  constructor
  · linarith
  · rcases (hmax w hw).eq_or_lt with rfl | hwv
    · exact hbw.2
    · exact hbw.2.trans (horder w hw v hv hwv).2

/-- Assemble ordered centers and transition cuts. The endpoint and overlap
conditions imply each closed interval between neighboring cuts lies in its
assigned neighborhood. -/
theorem exists_interval_chain {a b : ℝ} (hab : a ≤ b) (ρ : ℝ → ℝ)
    (hρ : ∀ t ∈ Set.Icc a b, 0 < ρ t) :
    ∃ n : ℕ, ∃ c : Fin (n + 1) → ℝ, ∃ q : Fin n → ℝ,
      StrictMono c ∧ (∀ i, c i ∈ Set.Icc a b) ∧
      a ∈ Set.Ioo (c 0 - ρ (c 0)) (c 0 + ρ (c 0)) ∧
      b ∈ Set.Ioo (c (Fin.last n) - ρ (c (Fin.last n)))
        (c (Fin.last n) + ρ (c (Fin.last n))) ∧
      ∀ i : Fin n, c i.castSucc < q i ∧ q i < c i.succ ∧
        q i ∈ Set.Ioo (c i.castSucc - ρ (c i.castSucc))
          (c i.castSucc + ρ (c i.castSucc)) ∧
        q i ∈ Set.Ioo (c i.succ - ρ (c i.succ))
          (c i.succ + ρ (c i.succ)) := by
  classical
  obtain ⟨s₀, hs₀, hcover₀⟩ := exists_finite_center_cover ρ hρ
  obtain ⟨s, hsub, hcover, hirr⟩ := exists_irredundant_subcover s₀
    (fun t => Set.Ioo (t - ρ t) (t + ρ t)) (Set.Icc a b) hcover₀
  have hcenters : ∀ t ∈ s, t ∈ Set.Icc a b := fun t ht => hs₀ t (hsub ht)
  have hrad : ∀ t ∈ s, 0 < ρ t := fun t ht => hρ t (hcenters t ht)
  have horder : ∀ u ∈ s, ∀ v ∈ s, u < v →
      u - ρ u < v - ρ v ∧ u + ρ u < v + ρ v := by
    intro u hu v hv huv
    exact endpoints_strictMono huv (hirr u hu v hv huv.ne)
      (hirr v hv u hu huv.ne')
  have hsne : s.Nonempty := by
    obtain ⟨t, ht, _⟩ := hcover a ⟨le_rfl, hab⟩
    exact ⟨t, ht⟩
  obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero (Finset.card_ne_zero.mpr hsne)
  let c : Fin (n + 1) ↪o ℝ := s.orderEmbOfFin hn
  have hcmem : ∀ i, c i ∈ s := fun i => s.orderEmbOfFin_mem hn i
  have hcsurj : ∀ w ∈ s, ∃ i, c i = w := by
    intro w hw
    have hw' : w ∈ Set.range (s.orderEmbOfFin hn) := by
      rw [s.range_orderEmbOfFin hn]
      exact hw
    exact hw'
  have hcuts : ∀ i : Fin n, ∃ q : ℝ,
      c i.castSucc < q ∧ q < c i.succ ∧
      q ∈ Set.Ioo (c i.castSucc - ρ (c i.castSucc))
        (c i.castSucc + ρ (c i.castSucc)) ∧
      q ∈ Set.Ioo (c i.succ - ρ (c i.succ))
        (c i.succ + ρ (c i.succ)) := by
    intro i
    have hi : c i.castSucc < c i.succ := c.strictMono (by simp)
    apply exists_transition_cut hi (hrad _ (hcmem _)) (hrad _ (hcmem _))
    apply adjacent_overlap hcenters hrad hcover horder (hcmem _) (hcmem _) hi
    intro w hw hiw
    obtain ⟨k, rfl⟩ := hcsurj w hw
    apply c.monotone
    have hik : i.castSucc < k := c.lt_iff_lt.mp hiw
    change i.val + 1 ≤ k.val
    exact hik
  choose q hq using hcuts
  refine ⟨n, c, q, c.strictMono, (fun i => hcenters _ (hcmem i)), ?_, ?_, hq⟩
  · apply left_endpoint_mem hab hcenters hrad hcover horder (hcmem 0)
    intro w hw
    obtain ⟨k, rfl⟩ := hcsurj w hw
    exact c.monotone (Fin.zero_le k)
  · apply right_endpoint_mem hab hcenters hrad hcover horder (hcmem (Fin.last n))
    intro w hw
    obtain ⟨k, rfl⟩ := hcsurj w hw
    exact c.monotone (Fin.le_last k)

end Problem326.IntervalChain

end

end OAI
