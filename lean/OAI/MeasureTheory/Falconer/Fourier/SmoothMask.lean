import OAI.MeasureTheory.Falconer.Angular.QuantitativeCaps

namespace OAI

/-!
# Smooth angular masks from buffered good sets

A finite subcollection of the normalized cap partition gives a cutoff
supported inside a prescribed set. It equals one wherever a closed ball
of twice the cap radius lies in that set. No regularity of the set is
needed for this finite construction.
-/

namespace Falconer
open Set
open scoped ContDiff
attribute [local instance] Classical.propDecidable

noncomputable def cutoffCapCenters {d : ℕ} (δ : ℝ) (S : Finset (Sphere d))
    (U : Set (Sphere d)) : Finset (Sphere d) :=
  S.filter (fun c => ∀ z : Sphere d, dist z c ≤ δ → z ∈ U)

noncomputable def capCutoffAmbient {d : ℕ} (δ : ℝ) (hδ : 0 < δ)
    (S : Finset (Sphere d)) (U : Set (Sphere d)) (x : Space d) : ℝ :=
  ∑ c ∈ cutoffCapCenters δ S U, normalizedCap δ hδ S c x

theorem capCutoffAmbient_contDiff {d : ℕ} {δ : ℝ} (hδ : 0 < δ)
    (S : Finset (Sphere d)) (U : Set (Sphere d)) :
    ContDiff ℝ ∞ (capCutoffAmbient δ hδ S U) :=
  ContDiff.sum (fun c _ => normalizedCap_contDiff hδ S c)

theorem capCutoffAmbient_properties {d : ℕ} {δ : ℝ} (hδ : 0 < δ)
    (S : Finset (Sphere d))
    (hcover : ∀ w : Sphere d, ∃ c ∈ S, dist w c ≤ δ/2) (U : Set (Sphere d)) :
    (∀ w : Sphere d, 0 ≤ capCutoffAmbient δ hδ S U w ∧ capCutoffAmbient δ hδ S U w ≤ 1) ∧
    (∀ w : Sphere d, capCutoffAmbient δ hδ S U w ≠ 0 → w ∈ U) ∧
    (∀ w : Sphere d, (∀ z : Sphere d, dist z w ≤ 2*δ → z ∈ U) →
      capCutoffAmbient δ hδ S U w = 1) := by
  obtain ⟨hpart,hbounds,hsupport⟩ := normalizedCap_properties hδ S hcover
  have hsub : cutoffCapCenters δ S U ⊆ S := Finset.filter_subset _ _
  refine ⟨?_,?_,?_⟩
  · intro w
    constructor
    · exact Finset.sum_nonneg (fun c hc => (hbounds c (hsub hc) w).1)
    · apply le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun c hc _ => (hbounds c hc w).1))
      exact (hpart w).le
  · intro w hw
    obtain ⟨c,hc,hcw⟩ := Finset.exists_ne_zero_of_sum_ne_zero hw
    have hsel := (Finset.mem_filter.mp hc).2
    apply hsel w
    exact hsupport c (hsub hc) w hcw
  · intro w hcore
    rw [← hpart w]
    apply Finset.sum_subset hsub
    intro c hc hnot
    by_contra hn
    have hdist : dist w c ≤ δ := hsupport c hc w hn
    apply hnot
    apply Finset.mem_filter.mpr ⟨hc,?_⟩
    intro z hz
    apply hcore z
    calc
      dist z w ≤ dist z c+dist c w := dist_triangle _ _ _
      _ ≤ δ+δ := add_le_add hz (by simpa only [dist_comm] using hdist)
      _ = 2*δ := by ring

end Falconer

end OAI
