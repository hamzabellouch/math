import OAI.Geometry.CylinderCovering.Convexity.OpenBaseComparison
import OAI.Geometry.CylinderCovering.Convexity.OpenBaseThickening

namespace OAI

noncomputable section
open Set MeasureTheory
namespace RuledApproximation

theorem Cylinder.enlarge_open_compact {C : Cylinder} (hC : IsCompact C.base)
    {eps : ℝ} (heps : 0 < eps) :
    ∃ D : Cylinder, D.axis = C.axis ∧ D.openBounded ∧
      C.carrier ⊆ D.carrier ∧ D.area < C.area + eps := by
  obtain ⟨O, hCO, hOo, hOb, hOm, hOI⟩ :=
    CylinderCovering.OpenBaseThickening.exists_open_enlargement volume hC heps
  refine ⟨⟨C.axis, C.unit_axis, O⟩, rfl, ⟨hOo, hOb, hOm⟩, ?_, hOI⟩
  rintro x ⟨b, hb, t, hx⟩
  exact ⟨b, hCO hb, t, hx⟩

theorem family_enlarge_open_compact {n : ℕ} (C : Fin n → Cylinder)
    (hC : ∀ i, IsCompact (C i).base) {eps : ℝ} (heps : 0 < eps) :
    ∃ D : Fin n → Cylinder, (∀ i, (D i).axis = (C i).axis) ∧
      (∀ i, (D i).openBounded) ∧ familySet C ⊆ familySet D ∧
      familyArea D ≤ familyArea C + eps := by
  classical
  have hd : 0 < eps / (n + 1 : ℝ) := div_pos heps (by positivity)
  choose D haxis hD hCD harea using fun i => Cylinder.enlarge_open_compact (hC i) hd
  refine ⟨D, haxis, hD, ?_, ?_⟩
  · intro x hx
    obtain ⟨i, hi⟩ := mem_iUnion.mp hx
    exact mem_iUnion.mpr ⟨i, hCD i hi⟩
  · change (∑ i, (D i).area) ≤ familyArea C + eps
    calc
      _ ≤ ∑ i, ((C i).area + eps / (n + 1 : ℝ)) :=
        Finset.sum_le_sum (fun i _ => (harea i).le)
      _ = familyArea C + n * (eps / (n + 1 : ℝ)) := by
        simp [familyArea, Finset.sum_add_distrib]
      _ ≤ familyArea C + eps := by
        have hn : 0 < (n + 1 : ℝ) := by positivity
        have hne : (n : ℝ) * (eps / (n + 1 : ℝ)) ≤ eps := by
          rw [← mul_div_assoc, div_le_iff₀ hn]
          nlinarith
        linarith

theorem family_enlarge_open_two_budgets {n : ℕ} (C : Fin n → Cylinder)
    (S : Set Space) (hC : ∀ i, IsCompact (C i).base) {A B : ℝ}
    (hA : familyArea C < A) (hB : familyRelativeArea C S < B) :
    ∃ D : Fin n → Cylinder, (∀ i, (D i).axis = (C i).axis) ∧
      (∀ i, (D i).openBounded) ∧ familySet C ⊆ familySet D ∧
      familyArea D < A ∧ familyRelativeArea D S < B := by
  classical
  have hw : (∑ i, ((C i).shadowArea S)⁻¹ * volume.real (C i).base) < B := by
    simpa only [familyRelativeArea, Cylinder.area, div_eq_mul_inv, mul_comm] using hB
  obtain ⟨U, hU, harea, hweighted⟩ :=
    CylinderCovering.OpenBaseThickening.exists_open_family_two_budgets
      (fun i => (volume : Measure ((Submodule.span ℝ ({(C i).axis} : Set Space))ᗮ)))
      (fun i => (C i).base) hC (fun i => ((C i).shadowArea S)⁻¹) hA hw
  let D : Fin n → Cylinder := fun i => ⟨(C i).axis, (C i).unit_axis, U i⟩
  refine ⟨D, fun _ => rfl, fun i => ⟨(hU i).2.1, (hU i).2.2.1, (hU i).2.2.2⟩,
    ?_, harea, ?_⟩
  · intro x hx
    obtain ⟨i, b, hb, t, ht⟩ := mem_iUnion.mp hx
    exact mem_iUnion.mpr ⟨i, b, (hU i).1 hb, t, ht⟩
  · simpa only [familyRelativeArea, Cylinder.area, Cylinder.shadowArea,
      D, div_eq_mul_inv, mul_comm] using hweighted

theorem openApproximation : OpenApproximationStatement := by
  intro n C S m hC hcov hm hshadow hcost
  have hrelative := familyRelativeArea_lt_half C S hm hshadow hcost
  obtain ⟨D, haxis, hopen, hCD, harea, hrel⟩ :=
    family_enlarge_open_two_budgets C S hC hcost hrelative
  exact ⟨D, haxis, hopen, hcov.trans hCD, harea, hrel⟩

end RuledApproximation

end

end OAI
