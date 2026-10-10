import Mathlib

namespace OAI

/-! A finite min/max sorting network for bounded stopping times. Unlike
sorting sampled values by a sample-dependent permutation, every output
is directly a stopping time. Ties and simultaneous switches are kept. -/

noncomputable section
open Set MeasureTheory
open scoped NNReal

namespace SLEExactGauge.Multipoint

def insertStop {Ω : Type*} (σ : Ω → ℝ≥0) : List (Ω → ℝ≥0) → List (Ω → ℝ≥0)
  | [] => [σ]
  | τ :: l => (fun ω => min (σ ω) (τ ω)) ::
      insertStop (fun ω => max (σ ω) (τ ω)) l

def sortStops {Ω : Type*} : List (Ω → ℝ≥0) → List (Ω → ℝ≥0)
  | [] => []
  | σ :: l => insertStop σ (sortStops l)

@[simp] lemma insertStop_length {Ω : Type*} (σ : Ω → ℝ≥0) (l : List (Ω → ℝ≥0)) :
    (insertStop σ l).length = l.length + 1 := by
  induction l generalizing σ with
  | nil => simp [insertStop]
  | cons τ l ih => simp [insertStop, ih]

@[simp] lemma sortStops_length {Ω : Type*} (l : List (Ω → ℝ≥0)) :
    (sortStops l).length = l.length := by
  induction l with
  | nil => rfl
  | cons σ l ih => simp [sortStops, ih]

lemma insertStop_lower_bound {Ω : Type*} (l : List (Ω → ℝ≥0)) (ω : Ω)
    (a : ℝ≥0) (σ : Ω → ℝ≥0) (hσ : a ≤ σ ω)
    (hl : ∀ τ ∈ l, a ≤ τ ω) : ∀ τ ∈ insertStop σ l, a ≤ τ ω := by
  induction l generalizing σ with
  | nil =>
    intro τ hτ
    have he : τ = σ := List.mem_singleton.mp hτ
    subst τ
    exact hσ
  | cons ρ l ih =>
    intro τ hτ
    rcases List.mem_cons.mp hτ with rfl | hτ
    · exact le_min hσ (hl ρ (List.mem_cons_self ..))
    · exact ih _ (hσ.trans (le_max_left _ _))
        (fun η hη => hl η (List.mem_cons_of_mem _ hη)) τ hτ

lemma insertStop_ordered {Ω : Type*} (l : List (Ω → ℝ≥0)) (ω : Ω)
    (hl : l.Pairwise (fun σ τ => σ ω ≤ τ ω)) (σ : Ω → ℝ≥0) :
    (insertStop σ l).Pairwise (fun σ τ => σ ω ≤ τ ω) := by
  induction l generalizing σ with
  | nil => simp [insertStop]
  | cons ρ l ih =>
    obtain ⟨hρ, hl⟩ := List.pairwise_cons.mp hl
    apply List.pairwise_cons.mpr
    refine ⟨?_, ih hl _⟩
    exact insertStop_lower_bound l ω (min (σ ω) (ρ ω)) _
      ((min_le_left _ _).trans (le_max_left _ _))
      (fun η hη => (min_le_right _ _).trans (hρ η hη))

theorem sortStops_ordered {Ω : Type*} (l : List (Ω → ℝ≥0)) (ω : Ω) :
    (sortStops l).Pairwise (fun σ τ => σ ω ≤ τ ω) := by
  induction l with
  | nil => simp [sortStops]
  | cons σ l ih => exact insertStop_ordered (sortStops l) ω ih σ

lemma insertStop_permutation {Ω : Type*} (l : List (Ω → ℝ≥0)) (ω : Ω)
    (σ : Ω → ℝ≥0) :
    ((insertStop σ l).map (fun τ => τ ω)).Perm (σ ω :: l.map (fun τ => τ ω)) := by
  induction l generalizing σ with
  | nil => simp [insertStop]
  | cons ρ l ih =>
    change (min (σ ω) (ρ ω) ::
      (insertStop (fun ω => max (σ ω) (ρ ω)) l).map (fun τ => τ ω)).Perm _
    apply ((ih (fun ω => max (σ ω) (ρ ω))).cons (min (σ ω) (ρ ω))).trans
    rcases le_total (σ ω) (ρ ω) with h | h
    · simp only [min_eq_left h, max_eq_right h, List.map_cons]
      exact List.Perm.refl _
    · simp only [min_eq_right h, max_eq_left h, List.map_cons]
      exact List.Perm.swap _ _ _

theorem sortStops_permutation {Ω : Type*} (l : List (Ω → ℝ≥0)) (ω : Ω) :
    ((sortStops l).map (fun τ => τ ω)).Perm (l.map (fun τ => τ ω)) := by
  induction l with
  | nil => simp [sortStops]
  | cons σ l ih =>
    exact (insertStop_permutation (sortStops l) ω σ).trans (ih.cons (σ ω))

lemma insertStop_bounded {Ω : Type*} (l : List (Ω → ℝ≥0)) (H : ℝ≥0)
    (σ : Ω → ℝ≥0) (hσ : ∀ ω, σ ω ≤ H)
    (hl : ∀ τ ∈ l, ∀ ω, τ ω ≤ H) : ∀ τ ∈ insertStop σ l, ∀ ω, τ ω ≤ H := by
  induction l generalizing σ with
  | nil =>
    intro τ hτ
    have he : τ = σ := List.mem_singleton.mp hτ
    subst τ
    exact hσ
  | cons ρ l ih =>
    intro τ hτ ω
    rcases List.mem_cons.mp hτ with rfl | hτ
    · exact (min_le_left _ _).trans (hσ ω)
    · exact ih _ (fun ω => max_le (hσ ω) (hl ρ (List.mem_cons_self ..) ω))
        (fun η hη => hl η (List.mem_cons_of_mem _ hη)) τ hτ ω

theorem sortStops_bounded {Ω : Type*} (l : List (Ω → ℝ≥0)) (H : ℝ≥0)
    (hl : ∀ τ ∈ l, ∀ ω, τ ω ≤ H) : ∀ τ ∈ sortStops l, ∀ ω, τ ω ≤ H := by
  induction l with
  | nil => simp [sortStops]
  | cons σ l ih =>
    apply insertStop_bounded (sortStops l) H σ (hl σ (List.mem_cons_self ..))
    exact ih (fun τ hτ => hl τ (List.mem_cons_of_mem _ hτ))

lemma insertStop_stopping {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (ℱ : Filtration ℝ≥0 mΩ) (l : List (Ω → ℝ≥0)) (σ : Ω → ℝ≥0)
    (hσ : IsStoppingTime ℱ (fun ω => (σ ω : WithTop ℝ≥0)))
    (hl : ∀ τ ∈ l, IsStoppingTime ℱ (fun ω => (τ ω : WithTop ℝ≥0))) :
    ∀ τ ∈ insertStop σ l, IsStoppingTime ℱ (fun ω => (τ ω : WithTop ℝ≥0)) := by
  induction l generalizing σ with
  | nil =>
    intro τ hτ
    have he : τ = σ := List.mem_singleton.mp hτ
    subst τ
    exact hσ
  | cons ρ l ih =>
    intro τ hτ
    have hρ := hl ρ (List.mem_cons_self ..)
    rcases List.mem_cons.mp hτ with rfl | hτ
    · simpa only [WithTop.coe_min] using hσ.min hρ
    · apply ih _ _ (fun η hη => hl η (List.mem_cons_of_mem _ hη)) τ hτ
      simpa only [WithTop.coe_max] using hσ.max hρ

theorem sortStops_stopping {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (ℱ : Filtration ℝ≥0 mΩ) (l : List (Ω → ℝ≥0))
    (hl : ∀ τ ∈ l, IsStoppingTime ℱ (fun ω => (τ ω : WithTop ℝ≥0))) :
    ∀ τ ∈ sortStops l, IsStoppingTime ℱ (fun ω => (τ ω : WithTop ℝ≥0)) := by
  induction l with
  | nil => simp [sortStops]
  | cons σ l ih =>
    apply insertStop_stopping ℱ (sortStops l) σ (hl σ (List.mem_cons_self ..))
    exact ih (fun τ hτ => hl τ (List.mem_cons_of_mem _ hτ))

def sortedStopAt {Ω : Type*} (l : List (Ω → ℝ≥0)) (H : ℝ≥0) (n : ℕ) : Ω → ℝ≥0 :=
  (sortStops l).getD n (fun _ => H)

theorem sortedStopAt_stopping {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (ℱ : Filtration ℝ≥0 mΩ) (l : List (Ω → ℝ≥0))
    (hl : ∀ τ ∈ l, IsStoppingTime ℱ (fun ω => (τ ω : WithTop ℝ≥0)))
    (H : ℝ≥0) (n : ℕ) : IsStoppingTime ℱ (fun ω => (sortedStopAt l H n ω : WithTop ℝ≥0)) := by
  by_cases hn : n < (sortStops l).length
  · rw [sortedStopAt, List.getD_eq_getElem _ _ hn]
    exact sortStops_stopping ℱ l hl _ (List.getElem_mem hn)
  · rw [sortedStopAt, List.getD_eq_default _ _ (Nat.le_of_not_gt hn)]
    exact isStoppingTime_const ℱ H

theorem sortedStopAt_bounded {Ω : Type*} (l : List (Ω → ℝ≥0)) (H : ℝ≥0)
    (hl : ∀ τ ∈ l, ∀ ω, τ ω ≤ H) (n : ℕ) (ω : Ω) : sortedStopAt l H n ω ≤ H := by
  by_cases hn : n < (sortStops l).length
  · rw [sortedStopAt, List.getD_eq_getElem _ _ hn]
    exact sortStops_bounded l H hl _ (List.getElem_mem hn) ω
  · rw [sortedStopAt, List.getD_eq_default _ _ (Nat.le_of_not_gt hn)]

theorem sortedStopAt_monotone {Ω : Type*} (l : List (Ω → ℝ≥0)) (H : ℝ≥0)
    (hl : ∀ τ ∈ l, ∀ ω, τ ω ≤ H) (ω : Ω) : Monotone (fun n => sortedStopAt l H n ω) := by
  intro i j hij
  by_cases hj : j < (sortStops l).length
  · have hi : i < (sortStops l).length := hij.trans_lt hj
    rcases eq_or_lt_of_le hij with rfl | hij
    · exact le_rfl
    · have h := (sortStops_ordered l ω).rel_get_of_lt
        (a := ⟨i, hi⟩) (b := ⟨j, hj⟩) hij
      simpa only [sortedStopAt, List.getD_eq_get _ _ ⟨i, hi⟩,
        List.getD_eq_get _ _ ⟨j, hj⟩] using h
  · have he : sortedStopAt l H j = fun _ => H :=
      List.getD_eq_default _ _ (Nat.le_of_not_gt hj)
    change sortedStopAt l H i ω ≤ sortedStopAt l H j ω
    rw [he]
    exact sortedStopAt_bounded l H hl i ω

@[simp] theorem sortedStopAt_length {Ω : Type*} (l : List (Ω → ℝ≥0)) (H : ℝ≥0) :
    sortedStopAt l H l.length = fun _ => H := by
  exact List.getD_eq_default _ _ (by simp)

/-- Every original switch occurs in the sorted sequence, including ties. -/
theorem sortedStopAt_covers {Ω : Type*} (l : List (Ω → ℝ≥0)) (H : ℝ≥0)
    (σ : Ω → ℝ≥0) (hσ : σ ∈ l) (ω : Ω) :
    ∃ n < l.length, sortedStopAt l H n ω = σ ω := by
  have hmem : σ ω ∈ (sortStops l).map (fun τ => τ ω) :=
    (sortStops_permutation l ω).mem_iff.mpr (List.mem_map_of_mem hσ)
  obtain ⟨τ, hτ, he⟩ := List.mem_map.mp hmem
  obtain ⟨i, hi⟩ := List.mem_iff_get.mp hτ
  refine ⟨i, by simpa only [sortStops_length] using i.isLt, ?_⟩
  rw [sortedStopAt, List.getD_eq_get _ _ i, hi, he]

theorem sortedStopAt_zero {Ω : Type*} (l : List (Ω → ℝ≥0)) (H : ℝ≥0)
    (hl : ∀ τ ∈ l, ∀ ω, τ ω ≤ H) (hzero : (fun _ : Ω => (0 : ℝ≥0)) ∈ l)
    (ω : Ω) : sortedStopAt l H 0 ω = 0 := by
  obtain ⟨n, _, hn⟩ := sortedStopAt_covers l H (fun _ => 0) hzero ω
  apply le_antisymm _ (show 0 ≤ sortedStopAt l H 0 ω from bot_le)
  have h := sortedStopAt_monotone l H hl ω (Nat.zero_le n)
  exact h.trans_eq hn

end SLEExactGauge.Multipoint

end

end OAI
