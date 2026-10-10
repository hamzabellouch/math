import OAI.Analysis.CircleDomains.Probability.RectangleMeasurability

namespace OAI

/-! Compact rectangles form a neighborhood basis inside a planar open
set; countably many of their interiors suffice to patch measurability. -/

open Set Function Filter MeasureTheory Metric
open scoped Topology

namespace CircleDomainRigidity

theorem exists_closed_rectangle_inside_open
    {U : Set (ℝ × ℝ)} (hU : IsOpen U) {p : ℝ × ℝ} (hp : p ∈ U) :
    ∃a b c d : ℝ, a < b ∧ c < d ∧ p ∈ Ioo a b ×ˢ Ioo c d ∧
      Icc a b ×ˢ Icc c d ⊆ U := by
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hp)
  refine ⟨p.1 - ε/2, p.1 + ε/2, p.2 - ε/2, p.2 + ε/2,
    by linarith, by linarith, ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩, ?_⟩
  intro q hq
  apply hball
  rw [Metric.mem_ball, Prod.dist_eq, max_lt_iff, Real.dist_eq, Real.dist_eq]
  constructor <;> apply abs_lt.mpr
  · constructor <;> linarith [hq.1.1, hq.1.2]
  · constructor <;> linarith [hq.2.1, hq.2.2]

theorem aestronglyMeasurable_on_open_of_rectangles
    {U : Set (ℝ × ℝ)} (hU : IsOpen U) (f : ℝ × ℝ → ℝ)
    (hf : ∀a b c d : ℝ, a < b → c < d → Icc a b ×ˢ Icc c d ⊆ U →
      AEStronglyMeasurable f (volume.restrict (Ioo a b ×ˢ Ioo c d))) :
    AEStronglyMeasurable f (volume.restrict U) := by
  choose a b c d hab hcd hp hsub using fun p : U => exists_closed_rectangle_inside_open hU p.property
  let R (p : U) := Ioo (a p) (b p) ×ˢ Ioo (c p) (d p)
  have hRo (p : U) : IsOpen (R p) := isOpen_Ioo.prod isOpen_Ioo
  have hRsub (p : U) : R p ⊆ U :=
    (Set.prod_mono Ioo_subset_Icc_self Ioo_subset_Icc_self).trans (hsub p)
  have heq : (⋃p : U, R p) = U := by
    apply Subset.antisymm
    · exact iUnion_subset hRsub
    · intro x hx
      exact mem_iUnion.mpr ⟨⟨x, hx⟩, hp ⟨x, hx⟩⟩
  obtain ⟨T, hT, hcover⟩ := TopologicalSpace.isOpen_iUnion_countable R hRo
  let : Countable T := hT.to_subtype
  have hpatch : AEStronglyMeasurable f (volume.restrict (⋃p : T, R p.val)) := by
    apply AEStronglyMeasurable.iUnion
    intro p
    exact hf _ _ _ _ (hab p.val) (hcd p.val) (hsub p.val)
  have hTU : (⋃p : T, R p.val) = U := by
    rw [iUnion_subtype, hcover, heq]
  rwa [hTU] at hpatch

end CircleDomainRigidity

end OAI
