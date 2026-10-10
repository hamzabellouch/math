import OAI.NumberTheory.JointDickman.Amplification.MajorArcPartition

namespace OAI

/-! # Cutting the major arcs at a finite denominator -/

namespace JointDickman
open Filter MeasureTheory Set Function
open scoped Topology

noncomputable def smallMajorArcRegion (B j : ℕ) (X : ℝ) (Q : ℕ) : Set ℝ :=
  ⋃ r : ℚ, if r.den ≤ Q then rationalArcPiece B j X r else ∅

noncomputable def largeMajorArcRegion (B j : ℕ) (X : ℝ) (Q : ℕ) : Set ℝ :=
  majorArcRegion B j X \ smallMajorArcRegion B j X Q

theorem smallMajorArcRegion_measurable (B j : ℕ) (X : ℝ) (Q : ℕ) :
    MeasurableSet (smallMajorArcRegion B j X Q) := by
  apply MeasurableSet.iUnion
  intro r
  split_ifs
  · exact rationalArcPiece_measurable B j X r
  · exact MeasurableSet.empty

theorem largeMajorArcRegion_measurable (B j : ℕ) (X : ℝ) (Q : ℕ) :
    MeasurableSet (largeMajorArcRegion B j X Q) :=
  (majorArcRegion_measurable B j X).diff (smallMajorArcRegion_measurable B j X Q)

theorem smallMajorArcRegion_subset (B j : ℕ) (X : ℝ) (Q : ℕ) :
    smallMajorArcRegion B j X Q ⊆ majorArcRegion B j X := by
  intro x hx
  obtain ⟨r,hr⟩ := mem_iUnion.mp hx
  split_ifs at hr with hq
  · exact ⟨hr.1,r,hr.2.1,hr.2.2⟩
  · exact hr.elim

theorem largeMajorArcRegion_witness {B j Q : ℕ} {X x : ℝ}
    (hx : x ∈ largeMajorArcRegion B j X Q) :
    ∃ r : ℚ, Q < r.den ∧ (r.den : ℝ) ≤ (B : ℝ)^12 ∧
      |-(j : ℝ)*x-(r : ℝ)| ≤ (B : ℝ)^13/X := by
  obtain ⟨r,hr,hnear⟩ := hx.1.2
  refine ⟨r,?_,hr,hnear⟩
  by_contra h
  have hq : r.den ≤ Q := le_of_not_gt h
  apply hx.2
  apply mem_iUnion.mpr
  exact ⟨r,by rw [ite_eq_left hq]; exact ⟨hx.1.1,hr,hnear⟩⟩

theorem majorArc_truncated_integral (B j Q : ℕ) (X : ℝ)
    {F : ℝ → ℂ} (hF : Continuous F) :
    (∫ x in majorArcRegion B j X, F x) =
      (∫ x in smallMajorArcRegion B j X Q, F x)+
        (∫ x in largeMajorArcRegion B j X Q, F x) := by
  have hI : IntegrableOn F (majorArcRegion B j X) :=
    (hF.intervalIntegrable 0 1).1.mono_set (fun _ hx => hx.1)
  have hsmall := smallMajorArcRegion_subset B j X Q
  have heq : majorArcRegion B j X =
      smallMajorArcRegion B j X Q ∪ largeMajorArcRegion B j X Q := by
    exact (union_sdiff_cancel hsmall).symm
  rw [heq]
  apply setIntegral_union
  · exact disjoint_sdiff_right
  · exact largeMajorArcRegion_measurable B j X Q
  · exact hI.mono_set hsmall
  · exact hI.mono_set sdiff_subset

end JointDickman

end OAI
