import OAI.Analysis.MassAction.CutDecomposition

namespace OAI

universe uV uE

/-! Finite directed-cut estimates used by the mass-action argument. -/

namespace Problem326.CutFlux

open scoped BigOperators

/-- A directed path leaving a set contains an edge leaving that set. -/
theorem transGen_crosses {V : Type uV} {r : V → V → Prop} {P : V → Prop}
    {u v : V} (h : Relation.TransGen r u v) (hu : P u) (hv : ¬ P v) :
    ∃ a b, r a b ∧ P a ∧ ¬ P b := by
  induction h with
  | single huv => exact ⟨_, _, huv, hu, hv⟩
  | @tail b c hab hbc ih =>
      by_cases hb : P b
      · exact ⟨b, c, hbc, hb, hv⟩
      · exact ih hb

/-- Every downward threshold crossing has an upward crossing when each edge
has a directed return path. No finiteness hypothesis is needed here. -/
theorem upward_of_downward {V : Type uV} {E : Type uE} (s t : E → V) (a : V → ℝ)
    (hreturn : ∀ e, Relation.TransGen
      (fun u v => ∃ f, s f = u ∧ t f = v) (t e) (s e))
    (c : ℝ) (e : E) (he : a (t e) ≤ c ∧ c < a (s e)) :
    ∃ f, a (s f) ≤ c ∧ c < a (t f) := by
  obtain ⟨u, v, huv, hu, hv⟩ :=
    transGen_crosses (P := fun z => a z ≤ c) (hreturn e) he.1
      (not_le.mpr he.2)
  obtain ⟨f, rfl, rfl⟩ := huv
  exact ⟨f, hu, lt_of_not_ge hv⟩

/-- The total upward flux across an ordered cut dominates the downward flux.
The rate assumption is phrased per edge, so it also handles an empty edge
set without introducing a minimum over the empty set. -/
theorem threshold_flux_nonneg_of_source_order {V : Type uV} {E : Type uE} [Fintype E]
    (s t : E → V) (a w : V → ℝ) (κ : E → ℝ) (δ : ℝ)
    (hreturn : ∀ e, Relation.TransGen
      (fun u v => ∃ f, s f = u ∧ t f = v) (t e) (s e))
    (hw : ∀ v, 0 < w v) (hκ : ∀ e, 0 < κ e) (hδ : 0 ≤ δ)
    (horder : ∀ e f, a (s e) < a (s f) → w (s f) ≤ δ * w (s e))
    (hrate : ∀ e, δ * (∑ f, κ f) < κ e) (c : ℝ) :
    0 ≤ (∑ e ∈ Finset.univ.filter (fun e => a (s e) ≤ c ∧ c < a (t e)),
          κ e * w (s e)) -
        (∑ e ∈ Finset.univ.filter (fun e => a (t e) ≤ c ∧ c < a (s e)),
          κ e * w (s e)) := by
  classical
  let U := Finset.univ.filter (fun e => a (s e) ≤ c ∧ c < a (t e))
  let D := Finset.univ.filter (fun e => a (t e) ≤ c ∧ c < a (s e))
  change 0 ≤ (∑ e ∈ U, κ e * w (s e)) - ∑ e ∈ D, κ e * w (s e)
  have hnonneg : ∀ e, 0 ≤ κ e * w (s e) :=
    fun e => mul_nonneg (hκ e).le (hw (s e)).le
  by_cases hD : D.Nonempty
  · obtain ⟨e, he⟩ := hD
    have he' : a (t e) ≤ c ∧ c < a (s e) := (Finset.mem_filter.mp he).2
    obtain ⟨f, hf⟩ := upward_of_downward s t a hreturn c e he'
    have hfU : f ∈ U := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hf⟩
    have hweights : ∀ g ∈ D, w (s g) ≤ δ * w (s f) := by
      intro g hg
      have hg' := (Finset.mem_filter.mp hg).2
      exact horder f g (lt_of_le_of_lt hf.1 hg'.2)
    have hsumD : (∑ g ∈ D, κ g * w (s g)) ≤
        (δ * w (s f)) * (∑ g ∈ D, κ g) := by
      calc
        (∑ g ∈ D, κ g * w (s g)) ≤ ∑ g ∈ D, κ g * (δ * w (s f)) :=
          Finset.sum_le_sum fun g hg => mul_le_mul_of_nonneg_left
            (hweights g hg) (hκ g).le
        _ = (δ * w (s f)) * (∑ g ∈ D, κ g) := by
          rw [← Finset.sum_mul, mul_comm]
    have hsumκ : (∑ g ∈ D, κ g) ≤ ∑ g, κ g := by
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ D)
        (fun g _ _ => (hκ g).le)
    have hdom : (∑ g ∈ D, κ g * w (s g)) < κ f * w (s f) := by
      calc
        (∑ g ∈ D, κ g * w (s g)) ≤
            (δ * w (s f)) * (∑ g ∈ D, κ g) := hsumD
        _ ≤ (δ * w (s f)) * (∑ g, κ g) :=
          mul_le_mul_of_nonneg_left hsumκ (mul_nonneg hδ (hw (s f)).le)
        _ < κ f * w (s f) := by
          nlinarith [mul_lt_mul_of_pos_right (hrate f) (hw (s f))]
    have hsingle : κ f * w (s f) ≤ ∑ g ∈ U, κ g * w (s g) :=
      Finset.single_le_sum (fun g _ => hnonneg g) hfU
    linarith
  · have hDe : D = ∅ := Finset.not_nonempty_iff_eq_empty.mp hD
    rw [hDe, Finset.sum_empty, sub_zero]
    exact Finset.sum_nonneg fun e _ => hnonneg e

/-- The all-vertex version of the threshold flux inequality. -/
theorem threshold_flux_nonneg {V : Type uV} {E : Type uE} [Fintype E]
    (s t : E → V) (a w : V → ℝ) (κ : E → ℝ) (δ : ℝ)
    (hreturn : ∀ e, Relation.TransGen
      (fun u v => ∃ f, s f = u ∧ t f = v) (t e) (s e))
    (hw : ∀ v, 0 < w v) (hκ : ∀ e, 0 < κ e) (hδ : 0 ≤ δ)
    (horder : ∀ u v, a u < a v → w v ≤ δ * w u)
    (hrate : ∀ e, δ * (∑ f, κ f) < κ e) (c : ℝ) :
    0 ≤ (∑ e ∈ Finset.univ.filter (fun e => a (s e) ≤ c ∧ c < a (t e)),
          κ e * w (s e)) -
        (∑ e ∈ Finset.univ.filter (fun e => a (t e) ≤ c ∧ c < a (s e)),
          κ e * w (s e)) := by
  exact threshold_flux_nonneg_of_source_order s t a w κ δ hreturn hw hκ hδ
    (fun e f => horder (s e) (s f)) hrate c

theorem total_flux_nonneg {V : Type uV} {E : Type uE} [Fintype E]
    (s t : E → V) (a w : V → ℝ) (κ : E → ℝ) (δ : ℝ)
    (hreturn : ∀ e, Relation.TransGen
      (fun u v => ∃ f, s f = u ∧ t f = v) (t e) (s e))
    (hw : ∀ v, 0 < w v) (hκ : ∀ e, 0 < κ e) (hδ : 0 ≤ δ)
    (horder : ∀ u v, a u < a v → w v ≤ δ * w u)
    (hrate : ∀ e, δ * (∑ f, κ f) < κ e) :
    0 ≤ ∑ e, κ e * w (s e) * (a (t e) - a (s e)) := by
  apply weighted_difference_nonneg_of_threshold_flux
    (fun e => a (s e)) (fun e => a (t e)) (fun e => κ e * w (s e))
  exact threshold_flux_nonneg s t a w κ δ hreturn hw hκ hδ horder hrate

theorem total_flux_nonneg_of_source_order {V : Type uV} {E : Type uE} [Fintype E]
    (s t : E → V) (a w : V → ℝ) (κ : E → ℝ) (δ : ℝ)
    (hreturn : ∀ e, Relation.TransGen
      (fun u v => ∃ f, s f = u ∧ t f = v) (t e) (s e))
    (hw : ∀ v, 0 < w v) (hκ : ∀ e, 0 < κ e) (hδ : 0 ≤ δ)
    (horder : ∀ e f, a (s e) < a (s f) → w (s f) ≤ δ * w (s e))
    (hrate : ∀ e, δ * (∑ f, κ f) < κ e) :
    0 ≤ ∑ e, κ e * w (s e) * (a (t e) - a (s e)) := by
  apply weighted_difference_nonneg_of_threshold_flux
    (fun e => a (s e)) (fun e => a (t e)) (fun e => κ e * w (s e))
  exact threshold_flux_nonneg_of_source_order s t a w κ δ hreturn hw hκ hδ horder hrate

end Problem326.CutFlux

end OAI
