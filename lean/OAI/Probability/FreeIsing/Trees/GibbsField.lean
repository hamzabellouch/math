import OAI.Probability.FreeIsing.Estimates.FiniteGibbsField
import OAI.Probability.FreeIsing.Estimates.FiniteMarginals
import OAI.Probability.FreeIsing.Trees.IncidentEdges

namespace OAI

noncomputable section

namespace Problem367

def finiteTreeEdges {d : ℕ} (D : Finset (TreeVertex d)) : Finset (D × D) := by
  classical
  exact Finset.univ.filter (fun e => (e.1.1, e.2.1) ∈ inducedEdges D)

private theorem pair_val_injective {d : ℕ} (D : Finset (TreeVertex d)) :
    Function.Injective (fun e : D × D => (e.1.1, e.2.1)) := by
  intro e f h
  exact Prod.ext (Subtype.ext (congrArg Prod.fst h)) (Subtype.ext (congrArg Prod.snd h))

theorem finiteTreeEdges_image {d : ℕ} (D : Finset (TreeVertex d)) :
    (finiteTreeEdges D).image (fun e => (e.1.1, e.2.1)) = inducedEdges D := by
  classical
  ext e
  constructor
  · rintro he
    obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp he
    simpa [finiteTreeEdges] using hf
  · intro he
    have heD : e.1 ∈ D ∧ e.2 ∈ D := by
      have hm := (Finset.mem_filter.mp he).1
      exact Finset.mem_product.mp hm
    refine Finset.mem_image.mpr ⟨(⟨e.1, heD.1⟩, ⟨e.2, heD.2⟩), ?_, rfl⟩
    simpa [finiteTreeEdges] using he

theorem finiteTreeEdges_incident_card {d : ℕ} (D : Finset (TreeVertex d)) (v : D) :
    ((finiteTreeEdges D).filter (fun e => e.1 = v ∨ e.2 = v)).card =
      ((inducedEdges D).filter (fun e => e.1 = v.1 ∨ e.2 = v.1)).card := by
  classical
  have he : (inducedEdges D).filter (fun e => e.1 = v.1 ∨ e.2 = v.1) =
      ((finiteTreeEdges D).filter (fun e => e.1 = v ∨ e.2 = v)).image
        (fun e => (e.1.1, e.2.1)) := by
    rw [← finiteTreeEdges_image D, Finset.filter_image]
    congr 1
    ext e
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨he, h | h⟩
      · exact ⟨he, Or.inl (Subtype.ext h)⟩
      · exact ⟨he, Or.inr (Subtype.ext h)⟩
    · rintro ⟨he, h | h⟩
      · exact ⟨he, Or.inl (congrArg Subtype.val h)⟩
      · exact ⟨he, Or.inr (congrArg Subtype.val h)⟩
  rw [he, Finset.card_image_of_injective _ (pair_val_injective D)]

theorem finiteInteractionEnergy_tree {d : ℕ} (D : Finset (TreeVertex d))
    (beta : ℝ) (eta : D → IsingSpin) :
    finiteInteractionEnergy (finiteTreeEdges D) beta eta =
      beta * ∑ e ∈ inducedEdges D,
        spinSign (extendFiniteSpin D eta e.1) * spinSign (extendFiniteSpin D eta e.2) := by
  classical
  rw [finiteInteractionEnergy, ← finiteTreeEdges_image D,
    Finset.sum_image (pair_val_injective D).injOn]
  simp

theorem finite_tree_gibbs_field_bound {d : ℕ} (D : Finset (TreeVertex d))
    {beta : ℝ} (hbeta : 0 ≤ beta) (y : D → ℝ) (v : D) :
    |Real.artanh (FinitePosterior.fieldMean
      (fun eta : D → IsingSpin => beta * ∑ e ∈ inducedEdges D,
        spinSign (extendFiniteSpin D eta e.1) * spinSign (extendFiniteSpin D eta e.2))
      (fun eta w => spinSign (eta w)) (fun eta => spinSign (eta v)) y) - y v| ≤
      (((inducedEdges D).filter (fun e => e.1 = v.1 ∨ e.2 = v.1)).card : ℝ) * beta := by
  classical
  have h := finite_gibbs_posterior_field_bound (finiteTreeEdges D) hbeta y v
  have he : finiteInteractionEnergy (finiteTreeEdges D) beta =
      (fun eta : D → IsingSpin => beta * ∑ e ∈ inducedEdges D,
        spinSign (extendFiniteSpin D eta e.1) * spinSign (extendFiniteSpin D eta e.2)) :=
    funext (finiteInteractionEnergy_tree D beta)
  rw [he, finiteTreeEdges_incident_card] at h
  exact h

theorem finite_tree_gibbs_field_uniform_bound {d : ℕ} (D : Finset (TreeVertex d))
    {beta : ℝ} (hbeta : 0 ≤ beta) (y : D → ℝ) (v : D) :
    |Real.artanh (FinitePosterior.fieldMean
      (fun eta : D → IsingSpin => beta * ∑ e ∈ inducedEdges D,
        spinSign (extendFiniteSpin D eta e.1) * spinSign (extendFiniteSpin D eta e.2))
      (fun eta w => spinSign (eta w)) (fun eta => spinSign (eta v)) y) - y v| ≤
      (d : ℝ) * beta := by
  apply (finite_tree_gibbs_field_bound D hbeta y v).trans
  apply mul_le_mul_of_nonneg_right _ hbeta
  exact_mod_cast card_incident_inducedEdges_le D v.1

end Problem367

end

end OAI
