import OAI.Analysis.CircleDomains.Modulus.LoopOscillationMinimum
import Mathlib.Topology.Order.DenselyOrdered

namespace OAI

/-! A diameter minimizer has no nonconstant closed subpath. -/
open Set Function Metric TopologicalSpace
open scoped Topology unitInterval
noncomputable section
namespace CircleDomainRigidity
variable {X : Type*} [MetricSpace X]

lemma dense_interval_closure {a b : unitInterval} (hab : a < b) :
    Icc a b ⊆ closure (Ioo a b ∩ range (denseSeq unitInterval)) := by
  have hsub : Ioo a b ⊆ closure (Ioo a b ∩ range (denseSeq unitInterval)) := by
    intro t ht
    apply isOpen_Ioo.inter_closure
    exact ⟨ht, (denseRange_denseSeq unitInterval) t⟩
  simpa only [closure_Ioo hab.ne, closure_closure] using closure_mono hsub

lemma nonconstant_loop_detected (g : C(unitInterval, X))
    {a b : unitInterval} (hab : a ≤ b)
    (hnc : ∃ u ∈ Icc a b, g u ≠ g a) :
    ∃ n, pathTestInterval n ⊆ Icc a b ∧ 0 < pathOscillation (pathTestInterval n) g := by
  have hlt : a < b := hab.lt_of_ne (by
    intro he
    subst b
    obtain ⟨u, hu, hne⟩ := hnc
    exact hne (congrArg g (le_antisymm hu.2 hu.1)))
  let D := Ioo a b ∩ range (denseSeq unitInterval)
  have hclosure : Icc a b ⊆ closure D := dense_interval_closure hlt
  have hD : D.Nonempty := by
    obtain ⟨t, ht, htr⟩ := (denseRange_denseSeq unitInterval).inter_open_nonempty
      (Ioo a b) isOpen_Ioo (nonempty_Ioo.mpr hlt)
    exact ⟨t, ht, htr⟩
  obtain ⟨c, hc⟩ := hD
  have hne : ∃ s ∈ D, ∃ t ∈ D, g s ≠ g t := by
    by_contra! hall
    have heq : closure D ⊆ {t | g t = g c} := by
      apply closure_minimal _ (isClosed_eq g.continuous continuous_const)
      exact fun t ht => hall t ht c hc
    obtain ⟨u, hu, hnu⟩ := hnc
    exact hnu ((heq (hclosure hu)).trans (heq (hclosure ⟨le_rfl, hab⟩)).symm)
  obtain ⟨s, hs, t, ht, hst⟩ := hne
  wlog hord : s ≤ t generalizing s t
  · exact this t ht s hs hst.symm (le_of_not_ge hord)
  obtain ⟨i, rfl⟩ := hs.2
  obtain ⟨j, rfl⟩ := ht.2
  refine ⟨Nat.pair i j, ?_, ?_⟩
  · simp only [pathTestInterval, Nat.unpair_pair]
    exact Icc_subset_Icc hs.1.1.le ht.1.2.le
  · change 0 < Metric.diam (g '' pathTestInterval (Nat.pair i j))
    apply Metric.diam_pos _ (path_image_isBounded _ _)
    refine ⟨g (denseSeq unitInterval i), ?_, g (denseSeq unitInterval j), ?_, hst⟩
    · exact mem_image_of_mem g (by simpa only [pathTestInterval, Nat.unpair_pair, mem_Icc] using And.intro le_rfl hord)
    · exact mem_image_of_mem g (by simpa only [pathTestInterval, Nat.unpair_pair, mem_Icc] using And.intro hord le_rfl)

lemma exists_loopless_path [CompleteSpace X] (f : C(unitInterval, X)) :
    ∃ g ∈ loopPathFamily f, ∀ a b : unitInterval, a ≤ b → g a = g b →
      ∀ u ∈ Icc a b, g u = g a := by
  obtain ⟨g, hg, hmin⟩ := exists_loopOscillation_minimum f
  refine ⟨g, hg, ?_⟩
  intro a b hab heq
  by_contra! hbad
  have hstrict := loopOscillationCost_erase_lt g hab heq (nonconstant_loop_detected g hab hbad)
  exact hstrict.not_ge (hmin _ (erasePathLoop_mem f g hg hab heq))

end CircleDomainRigidity

end

end OAI
