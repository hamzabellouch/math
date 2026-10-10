import OAI.MeasureTheory.Falconer.Estimates.PointSamples

namespace OAI

/-!
# The published Furstenberg input applied to sampled incidence lists

The original direction labels may repeat their coordinates and may have
different covering families. All geometric lines are rounded to one grid
before applying the published cardinality bound.
-/

namespace Falconer
open Set
attribute [local instance] Classical.propDecidable

theorem sampled_furstenberg_obstruction
    (hpublished : PublishedPlanarFurstenberg) {b f : ℝ}
    (hb : 0 < b) (hb' : b ≤ 1 / 2) (hbf : b < f) (hf : f < 1) :
    ∃ ε δ₀ : ℝ, 0 < ε ∧ 0 < δ₀ ∧ δ₀ ≤ 1 / 2 ∧
    ∀ δ : ℝ, 0 < δ → δ < δ₀ →
    ∀ P : Finset (Space 2), P.Nonempty →
      (∀ x ∈ P, |x 0| ≤ 1 / 4 ∧ |x 1| ≤ 1 / 4) →
      FiniteSeparatedAt δ P → NormalizedFiniteBallBound δ f (δ^(-ε)) P →
    ∀ (ι : Type) [DecidableEq ι] (D : Finset ι) (m : ι → ℝ)
      (S : Space 2 → Finset ι) (U : ι → Finset (Space 2)) (K I : ℝ),
      0 < K → 0 < I → D.Nonempty →
      (D.card : ℝ) * δ^b ≤ 2 →
      (∀ i ∈ D, |m i| ≤ 1 / 2) →
      (∀ a r : ℝ, δ ≤ r → ((D.filter (fun i => |m i-a| ≤ r)).card : ℝ) ≤
        (K * (D.card : ℝ)) * r^b) →
      (∀ x ∈ P, S x ⊆ D ∧ I * (D.card : ℝ) ≤ ((S x).card : ℝ)) →
      2 * 2^b * K^2 / I ≤ δ^(-ε) →
      (D.card : ℝ) ≤ δ^(-b-ε/4) →
      (∀ i ∈ D, ((U i).card : ℝ) ≤ δ^(-b-ε/4)) →
      (∀ x ∈ P, ∀ i ∈ S x, roundedIncidentLine δ x (m i) ∈ U i) → False := by
  obtain ⟨ε, δ₁, hε, hδ₁, _, hF⟩ :=
    published_furstenberg_labelled_obstruction hpublished hb hb' hbf hf
  refine ⟨ε, min δ₁ (1/2), hε, lt_min hδ₁ (by norm_num), min_le_right _ _, ?_⟩
  intro δ hδ hδsmall P hP hchart hsep hpoint ι _ D m S U K I hK hI hD
    hsize hm hcount hS hloss hDcard hU hcover
  have hδ1 : δ ≤ 1 / 2 := hδsmall.le.trans (min_le_right _ _)
  let T : Space 2 → Finset (Space 2) := fun x => roundedLineFamily δ x m (S x)
  have hT (x : Space 2) (hx : x ∈ P) :
      (T x).Nonempty ∧ InBoundedLineChart (T x) ∧ FiniteSeparatedAt δ (T x) ∧
      NormalizedFiniteBallBound δ b (δ^(-ε)) (T x) ∧
      ∀ l ∈ T x, TubeIncident δ x l := by
    have hSn : (S x).Nonempty := by
      apply Finset.card_pos.mp
      have hn : (0 : ℝ) < D.card := by exact_mod_cast hD.card_pos
      have hspos := (mul_pos hI hn).trans_le (hS x hx).2
      exact_mod_cast hspos
    refine ⟨roundedLineFamily_nonempty δ x m hSn, ?_,
      roundedIncidentLine_family_separated hδ x m (S x), ?_, ?_⟩
    · intro l hl
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hl
      exact roundedIncidentLine_in_chart hδ hδ1 x (hchart x hx).1 (hchart x hx).2
        (m i) (hm i ((hS x hx).1 hi))
    · have hn := roundedLineFamily_normalized_of_large_sample hδ hK hI x m D (S x)
        hD (hS x hx).1 hsize (hS x hx).2 hcount
      intro z r hδr hr
      apply (hn z r hδr hr).trans
      apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _)
      exact mul_le_mul_of_nonneg_right hloss (Real.rpow_nonneg (hδ.trans_le hδr).le _)
    · intro l hl
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hl
      exact roundedIncidentLine_incident hδ x (m i)
  have hPchart : InBoundedLineChart P := by
    intro x hx
    exact ⟨(hchart x hx).1.trans (by norm_num), (hchart x hx).2.trans (by norm_num)⟩
  apply hF δ hδ (hδsmall.trans_le (min_le_left _ _)) P hP hPchart hsep hpoint T hT
    ι D U hDcard hU
  intro x hx l hl
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hl
  exact ⟨i, (hS x hx).1 hi, hcover x hx i hi⟩

end Falconer

end OAI
