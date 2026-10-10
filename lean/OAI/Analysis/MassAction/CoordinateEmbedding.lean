import OAI.Analysis.MassAction.FixedMinimum

namespace OAI

noncomputable section
open scoped BigOperators
open Filter Topology

namespace Problem326.Affine

local instance {d : ℕ} : DecidableEq (Label d) := Classical.decEq _

/-- Extend coordinates along an injection, using the constant baseline on its complement. -/
def embedCoordinates {k d : ℕ} (e : Fin k ↪ Fin d) (t : ℝ)
    (s : Fin k → ℝ) : Fin d → ℝ :=
  fun i => t + ∑ j, if e j = i then s j - t else 0

@[simp] theorem embedCoordinates_apply {k d : ℕ} (e : Fin k ↪ Fin d)
    (t : ℝ) (s : Fin k → ℝ) (j : Fin k) :
    embedCoordinates e t s (e j) = s j := by
  classical
  simp only [embedCoordinates, e.injective.eq_iff]
  simp

theorem embedCoordinates_outside {k d : ℕ} (e : Fin k ↪ Fin d)
    (t : ℝ) (s : Fin k → ℝ) {i : Fin d} (hi : i ∉ Set.range e) :
    embedCoordinates e t s i = t := by
  classical
  have hne (j : Fin k) : e j ≠ i := fun h => hi ⟨j, h⟩
  simp [embedCoordinates, hne]

/-- The larger-dimensional label used for a fixed-minimum type. -/
def Label.embed {k d : ℕ} (e : Fin k ↪ Fin d) (t β : ℝ)
    (L : Label k) : Label d where
  slope := embedCoordinates e t L.slope
  offset := fun h => -h ^ β + L.offset h

theorem embedCoordinates_dot {k d : ℕ} (e : Fin k ↪ Fin d)
    (t : ℝ) (s : Fin k → ℝ) (x : Fin d → ℝ) :
    (∑ i, embedCoordinates e t s i * x i) =
      (∑ j, s j * x (e j)) + t * ((∑ i, x i) - ∑ j, x (e j)) := by
  classical
  simp only [embedCoordinates, add_mul, Finset.sum_add_distrib]
  have hex : (∑ i : Fin d, (∑ j : Fin k, if e j = i then s j - t else 0) * x i) =
      ∑ j : Fin k, (s j - t) * x (e j) := by
    simp_rw [Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j hj
    simp [ite_mul]
  rw [hex]
  simp only [sub_mul, Finset.sum_sub_distrib, ← Finset.mul_sum]
  ring

/-- Embedded affine values differ from their projected values by a common term. -/
theorem Label.embed_value {k d : ℕ} (e : Fin k ↪ Fin d) (t β h : ℝ)
    (L : Label k) (x : Fin d → ℝ) :
    (L.embed e t β).value h x = L.value h (fun j => x (e j)) +
      t * ((∑ i, x i) - ∑ j, x (e j)) - h ^ β := by
  dsimp [Label.value, Label.embed]
  rw [embedCoordinates_dot]
  ring

theorem Label.embed_injective {k d : ℕ} (e : Fin k ↪ Fin d) (t β : ℝ) :
    Function.Injective (Label.embed e t β) := by
  intro L J heq
  have hs : L.slope = J.slope := by
    funext j
    have hj := congrArg (fun Q : Label d => Q.slope (e j)) heq
    simpa only [Label.embed, embedCoordinates_apply] using hj
  have hc : L.offset = J.offset := by
    funext h
    have hh := congrArg (fun Q : Label d => Q.offset h) heq
    dsimp [Label.embed] at hh
    linarith
  cases L
  cases J
  cases hs
  cases hc
  rfl

/-- Common baseline and offset terms preserve all comparisons, including ties. -/
theorem active_embed_iff {k d : ℕ} (e : Fin k ↪ Fin d) (t β h : ℝ)
    (Λ : Finset (Label k)) (L : Label k) (x : Fin d → ℝ) :
    Active (Λ.image (Label.embed e t β)) (L.embed e t β) h x ↔
      Active Λ L h (fun j => x (e j)) := by
  classical
  constructor
  · intro ha
    obtain ⟨J, hJ, hJL⟩ := Finset.mem_image.1 ha.1
    have hJL' : J = L := Label.embed_injective e t β hJL
    subst J
    refine ⟨hJ, ?_⟩
    intro J hJ
    have hh := ha.2 (J.embed e t β) (Finset.mem_image_of_mem _ hJ)
    simp only [Label.embed_value] at hh
    linarith
  · intro ha
    refine ⟨Finset.mem_image_of_mem _ ha.1, ?_⟩
    intro J hJ
    obtain ⟨Q, hQ, rfl⟩ := Finset.mem_image.1 hJ
    have hh := ha.2 Q hQ
    simp only [Label.embed_value]
    linarith

theorem cube_embedCoordinates {k d : ℕ} (e : Fin k ↪ Fin d)
    {a t β b : ℝ} {s : Fin k → ℝ}
    (hat : a ≤ t) (htβ : t ≤ β) (htb : t ≤ b) (hs : Cube β b s) :
    Cube a b (embedCoordinates e t s) := by
  intro i
  by_cases hi : i ∈ Set.range e
  · obtain ⟨j, rfl⟩ := hi
    rw [embedCoordinates_apply]
    exact ⟨hat.trans (htβ.trans (hs j).1), (hs j).2⟩
  · rw [embedCoordinates_outside e t s hi]
    exact ⟨hat, htb⟩

theorem hasMinimum_embedCoordinates {k d : ℕ} (e : Fin k ↪ Fin d)
    (hkd : k < d) {t : ℝ} {s : Fin k → ℝ} (hs : ∀ j, t ≤ s j) :
    HasMinimum (embedCoordinates e t s) t := by
  constructor
  · intro i
    by_cases hi : i ∈ Set.range e
    · obtain ⟨j, rfl⟩ := hi
      simpa only [embedCoordinates_apply] using hs j
    · rw [embedCoordinates_outside e t s hi]
  · have hns : ¬ Function.Surjective e := by
      intro hsurj
      have hcard := Fintype.card_le_of_surjective e hsurj
      simp only [Fintype.card_fin] at hcard
      omega
    change ¬ ∀ i, ∃ j, e j = i at hns
    push Not at hns
    obtain ⟨i, hi⟩ := hns
    refine ⟨i, embedCoordinates_outside e t s ?_⟩
    simpa only [Set.mem_range, not_exists] using hi

/-- The raised coordinates of the embedded slope are exactly the injected coordinates. -/
theorem embedCoordinates_gt_baseline_iff {k d : ℕ} (e : Fin k ↪ Fin d)
    {t : ℝ} {s : Fin k → ℝ} (hs : ∀ j, t < s j) (i : Fin d) :
    t < embedCoordinates e t s i ↔ i ∈ Set.range e := by
  by_cases hi : i ∈ Set.range e
  · obtain ⟨j, rfl⟩ := hi
    exact iff_of_true (by simpa only [embedCoordinates_apply] using hs j) ⟨j, rfl⟩
  · rw [embedCoordinates_outside e t s hi]
    simp [hi]

theorem tendsto_project_coordinates {k d : ℕ} (e : Fin k ↪ Fin d)
    {p : ℕ → (Fin d → ℝ)} {p₀ : Fin d → ℝ}
    (hp : Tendsto p atTop (𝓝 p₀)) :
    Tendsto (fun n j => p n (e j)) atTop (𝓝 (fun j => p₀ (e j))) := by
  exact tendsto_pi_nhds.2 (fun j => (tendsto_pi_nhds.1 hp) (e j))

theorem powerPoint_project {k d : ℕ} (e : Fin k ↪ Fin d)
    (h : ℝ) (p : Fin d → ℝ) :
    (fun j => powerPoint h p (e j)) = powerPoint h (fun j => p (e j)) := rfl

/-- Activity in any larger family restricts to the projected lower-dimensional family. -/
theorem active_project_of_active {k d : ℕ} (e : Fin k ↪ Fin d) (t β h : ℝ)
    {Λ : Finset (Label k)} {Γ : Finset (Label d)} {L : Label k}
    (hΛ : Λ.image (Label.embed e t β) ⊆ Γ) (hL : L ∈ Λ)
    (p : Fin d → ℝ)
    (ha : Active Γ (L.embed e t β) h (powerPoint h p)) :
    Active Λ L h (powerPoint h (fun j => p (e j))) := by
  have ha' := active_mono hΛ (Finset.mem_image_of_mem _ hL) ha
  have hp := (active_embed_iff e t β h Λ L (powerPoint h p)).1 ha'
  simpa only [powerPoint_project] using hp

/-- A projected norm estimate controls every raised coordinate of the larger slope. -/
theorem embedded_error_on_range {k d : ℕ} (e : Fin k ↪ Fin d)
    (t : ℝ) {s : Fin k → ℝ} {p : Fin d → ℝ} {ε : ℝ}
    (herr : ‖(fun j => p (e j)) - s‖ < ε) :
    ∀ i ∈ Set.range e, |p i - embedCoordinates e t s i| < ε := by
  have hε : 0 < ε := (norm_nonneg _).trans_lt herr
  have hh := (pi_norm_lt_iff hε).1 herr
  intro i hi
  obtain ⟨j, rfl⟩ := hi
  simpa only [embedCoordinates_apply, Pi.sub_apply, Real.norm_eq_abs] using hh j

/-- Canonical coordinate injection for a finite support, built from its finite enumeration. -/
def supportEmbedding {d : ℕ} (U : Finset (Fin d)) : Fin U.card ↪ Fin d :=
  U.equivFin.symm.toEmbedding.trans (Function.Embedding.subtype (fun i => i ∈ U))

@[simp] theorem supportEmbedding_mem {d : ℕ} (U : Finset (Fin d)) (j : Fin U.card) :
    supportEmbedding U j ∈ U :=
  (U.equivFin.symm j).property

theorem range_supportEmbedding {d : ℕ} (U : Finset (Fin d)) :
    Set.range (supportEmbedding U) = (U : Set (Fin d)) := by
  ext i
  constructor
  · rintro ⟨j, rfl⟩
    exact supportEmbedding_mem U j
  · intro hi
    refine ⟨U.equivFin ⟨i, hi⟩, ?_⟩
    simp [supportEmbedding]

/-- Every member of an embedded nonempty family has the required baseline minimum. -/
theorem embedded_family_data {k d : ℕ} (e : Fin k ↪ Fin d)
    (hkd : k < d) {a t β b : ℝ}
    (hat : a ≤ t) (htβ : t < β) (hβb : β < b)
    (Λ : Finset (Label k)) (hne : Λ.Nonempty)
    (hslopes : ∀ L ∈ Λ, Cube β b L.slope) :
    (Λ.image (Label.embed e t β)).Nonempty ∧
      ∀ J ∈ Λ.image (Label.embed e t β),
        Cube a b J.slope ∧ HasMinimum J.slope t ∧
        ∀ i, t < J.slope i ↔ i ∈ Set.range e := by
  classical
  refine ⟨hne.image _, ?_⟩
  intro J hJ
  obtain ⟨L, hL, rfl⟩ := Finset.mem_image.1 hJ
  refine ⟨cube_embedCoordinates e hat htβ.le (htβ.trans hβb).le (hslopes L hL), ?_, ?_⟩
  · exact hasMinimum_embedCoordinates e hkd (fun j => htβ.le.trans (hslopes L hL j).1)
  · exact embedCoordinates_gt_baseline_iff e (fun j => htβ.trans_le (hslopes L hL j).1)

end Problem326.Affine

end

end OAI
