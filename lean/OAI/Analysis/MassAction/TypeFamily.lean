import OAI.Analysis.MassAction.CoordinateEmbedding

namespace OAI

noncomputable section
open scoped BigOperators
open Filter Topology

namespace Problem326.Affine

local instance {d : ℕ} : DecidableEq (Label d) := Classical.decEq _

/-- The type-`k` family is the finite union over coordinate injections. Indexing by all
injections avoids dependent coordinate casts; every `k`-element support is represented. -/
def typeFamily {k d : ℕ} (t β : ℝ)
    (Λ : (Fin k ↪ Fin d) → Finset (Label k)) : Finset (Label d) :=
  Finset.univ.biUnion (fun e => (Λ e).image (Label.embed e t β))

theorem mem_typeFamily {k d : ℕ} (t β : ℝ)
    (Λ : (Fin k ↪ Fin d) → Finset (Label k)) (J : Label d) :
    J ∈ typeFamily t β Λ ↔
      ∃ e : Fin k ↪ Fin d, ∃ L ∈ Λ e, L.embed e t β = J := by
  classical
  simp only [typeFamily, Finset.mem_biUnion, Finset.mem_univ, true_and,
    Finset.mem_image]

theorem embeddedFamily_subset_typeFamily {k d : ℕ} (t β : ℝ)
    (Λ : (Fin k ↪ Fin d) → Finset (Label k)) (e : Fin k ↪ Fin d) :
    (Λ e).image (Label.embed e t β) ⊆ typeFamily t β Λ := by
  intro J hJ
  obtain ⟨L, hL, rfl⟩ := Finset.mem_image.1 hJ
  exact (mem_typeFamily t β Λ _).2 ⟨e, L, hL, rfl⟩

theorem typeFamily_nonempty {k d : ℕ} (hkd : k ≤ d) (t β : ℝ)
    (Λ : (Fin k ↪ Fin d) → Finset (Label k))
    (hne : ∀ e, (Λ e).Nonempty) : (typeFamily t β Λ).Nonempty := by
  let e : Fin k ↪ Fin d := Fin.castLEEmb hkd
  obtain ⟨L, hL⟩ := hne e
  exact ⟨L.embed e t β, (mem_typeFamily t β Λ _).2 ⟨e, L, hL, rfl⟩⟩

/-- Every member of a type family has baseline minimum and exactly the injected raised support. -/
theorem typeFamily_member_data {k d : ℕ} (hkd : k < d)
    {a t β b : ℝ} (hat : a ≤ t) (htβ : t < β) (hβb : β < b)
    (Λ : (Fin k ↪ Fin d) → Finset (Label k))
    (hslopes : ∀ e L, L ∈ Λ e → Cube β b L.slope)
    {J : Label d} (hJ : J ∈ typeFamily t β Λ) :
    Cube a b J.slope ∧ HasMinimum J.slope t ∧
      ∃ e : Fin k ↪ Fin d, ∀ i, t < J.slope i ↔ i ∈ Set.range e := by
  obtain ⟨e, L, hL, rfl⟩ := (mem_typeFamily t β Λ J).1 hJ
  refine ⟨cube_embedCoordinates e hat htβ.le (htβ.trans hβb).le (hslopes e L hL),
    hasMinimum_embedCoordinates e hkd (fun j => htβ.le.trans (hslopes e L hL j).1), e, ?_⟩
  exact embedCoordinates_gt_baseline_iff e (fun j => htβ.trans_le (hslopes e L hL j).1)

/-- Every prescribed support of size `k` occurs in the type family. -/
theorem typeFamily_support_exists {k d : ℕ} {t β b : ℝ} (htβ : t < β)
    (Λ : (Fin k ↪ Fin d) → Finset (Label k))
    (hne : ∀ e, (Λ e).Nonempty)
    (hslopes : ∀ e L, L ∈ Λ e → Cube β b L.slope)
    (U : Finset (Fin d)) (hU : U.card = k) :
    ∃ J ∈ typeFamily t β Λ, ∀ i, t < J.slope i ↔ i ∈ U := by
  let e : Fin k ↪ Fin d := (U.orderEmbOfFin hU).toEmbedding
  obtain ⟨L, hL⟩ := hne e
  refine ⟨L.embed e t β, (mem_typeFamily t β Λ _).2 ⟨e, L, hL, rfl⟩, ?_⟩
  intro i
  change t < embedCoordinates e t L.slope i ↔ i ∈ U
  rw [embedCoordinates_gt_baseline_iff e (fun j => htβ.trans_le (hslopes e L hL j).1)]
  have hrange : Set.range e = (U : Set (Fin d)) := Finset.range_orderEmbOfFin U hU
  rw [hrange]
  rfl

/-- All comparisons in the total type family imply the lower-dimensional activity hypothesis. -/
theorem typeFamily_active_project {k d : ℕ} (t β h : ℝ)
    (Λ : (Fin k ↪ Fin d) → Finset (Label k))
    (e : Fin k ↪ Fin d) {L : Label k} (hL : L ∈ Λ e)
    (p : Fin d → ℝ)
    (ha : Active (typeFamily t β Λ) (L.embed e t β) h (powerPoint h p)) :
    Active (Λ e) L h (powerPoint h (fun j => p (e j))) :=
  active_project_of_active e t β h (embeddedFamily_subset_typeFamily t β Λ e) hL p ha

/-- The support data in finite-set form, matching the layer-certificate interface. -/
theorem typeFamily_support_data {k d : ℕ} (t β : ℝ)
    (Λ : (Fin k ↪ Fin d) → Finset (Label k)) {b : ℝ}
    (hslopes : ∀ e L, L ∈ Λ e → Cube β b L.slope)
    {J : Label d} (hJ : J ∈ typeFamily t β Λ) :
    ∃ U : Finset (Fin d), U.card = k ∧
      (∀ i ∈ U, β ≤ J.slope i ∧ J.slope i ≤ b) ∧
      (∀ i ∉ U, J.slope i = t) := by
  classical
  obtain ⟨e, L, hL, rfl⟩ := (mem_typeFamily t β Λ J).1 hJ
  refine ⟨Finset.univ.map e, by simp, ?_, ?_⟩
  · intro i hi
    obtain ⟨j, hj, rfl⟩ := Finset.mem_map.1 hi
    simpa only [Label.embed, embedCoordinates_apply] using hslopes e L hL j
  · intro i hi
    apply embedCoordinates_outside e t L.slope
    rintro ⟨j, rfl⟩
    exact hi (Finset.mem_map.2 ⟨j, Finset.mem_univ j, rfl⟩)

/-- Every support has a competitor equal to the baseline off that support. -/
theorem typeFamily_supported_competitor {k d : ℕ} (t β : ℝ)
    (Λ : (Fin k ↪ Fin d) → Finset (Label k))
    (hne : ∀ e, (Λ e).Nonempty)
    (U : Finset (Fin d)) (hU : U.card = k) :
    ∃ J ∈ typeFamily t β Λ, ∀ i ∉ U, J.slope i = t := by
  classical
  let e : Fin k ↪ Fin d := (U.orderEmbOfFin hU).toEmbedding
  obtain ⟨L, hL⟩ := hne e
  refine ⟨L.embed e t β, (mem_typeFamily t β Λ _).2 ⟨e, L, hL, rfl⟩, ?_⟩
  intro i hi
  apply embedCoordinates_outside e t L.slope
  have hrange : Set.range e = (U : Set (Fin d)) := Finset.range_orderEmbOfFin U hU
  simpa only [hrange, Finset.mem_coe] using hi

/-- A lower-dimensional little-offset quotient becomes the normalized `-1` offset
required of a positive type. -/
theorem Label.embed_normalized_offset {k d : ℕ} (e : Fin k ↪ Fin d)
    (t β : ℝ) (L : Label k)
    (hL : Tendsto (fun h : ℝ => L.offset h / h ^ β) (𝓝[>] 0) (𝓝 0)) :
    Tendsto (fun h : ℝ => (L.embed e t β).offset h / h ^ β)
      (𝓝[>] 0) (𝓝 (-1)) := by
  have heq : (fun h : ℝ => (L.embed e t β).offset h / h ^ β) =ᶠ[𝓝[>] 0]
      (fun h : ℝ => -1 + L.offset h / h ^ β) := by
    filter_upwards [self_mem_nhdsWithin] with h hh
    change (-h ^ β + L.offset h) / h ^ β = -1 + L.offset h / h ^ β
    rw [add_div, neg_div, div_self (ne_of_gt (Real.rpow_pos_of_pos hh β))]
  have ht : Tendsto (fun h : ℝ => -1 + L.offset h / h ^ β)
      (𝓝[>] 0) (𝓝 (-1)) := by
    simpa using tendsto_const_nhds.add hL
  exact ht.congr' heq.symm

end Problem326.Affine

end

end OAI
