import OAI.Analysis.CircleDomains.Topology.PathLoopErasure
import Mathlib.Topology.MetricSpace.Lipschitz

namespace OAI

/-! The diameter of a path image on a fixed parameter set is continuous
in the uniform metric. Loop deletion decreases every interval diameter. -/
open Set Function Metric Bornology
open scoped Topology unitInterval NNReal
noncomputable section
namespace CircleDomainRigidity
variable {X : Type*} [MetricSpace X]

def pathOscillation (S : Set unitInterval) (g : C(unitInterval, X)) : ℝ :=
  Metric.diam (g '' S)

lemma path_image_isBounded (S : Set unitInterval) (g : C(unitInterval, X)) :
    IsBounded (g '' S) :=
  (isCompact_range g.continuous).isBounded.subset (image_subset_range g S)

lemma pathOscillation_le_add (S : Set unitInterval) (g h : C(unitInterval, X)) :
    pathOscillation S g ≤ pathOscillation S h + 2 * dist g h := by
  apply diam_le_of_forall_dist_le (by unfold pathOscillation; positivity)
  rintro _ ⟨s, hs, rfl⟩ _ ⟨t, ht, rfl⟩
  have h₁ := ContinuousMap.dist_apply_le_dist (f := g) (g := h) s
  have h₂ := ContinuousMap.dist_apply_le_dist (f := g) (g := h) t
  have h₃ := dist_le_diam_of_mem (path_image_isBounded S h)
    (mem_image_of_mem h hs) (mem_image_of_mem h ht)
  have h₄ := dist_triangle (g s) (h s) (g t)
  have h₅ := dist_triangle (h s) (h t) (g t)
  rw [dist_comm (h t) (g t)] at h₅
  dsimp [pathOscillation] at *
  linarith

lemma lipschitzWith_pathOscillation (S : Set unitInterval) :
    LipschitzWith 2 (pathOscillation (X := X) S) := by
  apply LipschitzWith.of_dist_le_mul
  intro g h
  rw [Real.dist_eq]
  have h₁ := pathOscillation_le_add S g h
  have h₂ := pathOscillation_le_add S h g
  rw [dist_comm h g] at h₂
  change |pathOscillation S g - pathOscillation S h| ≤ 2 * dist g h
  exact abs_le.mpr ⟨by linarith, by linarith⟩

lemma continuous_pathOscillation (S : Set unitInterval) :
    Continuous (pathOscillation (X := X) S) :=
  (lipschitzWith_pathOscillation S).continuous

lemma pathOscillation_erase_le (g : C(unitInterval, X))
    {a b : unitInterval} (hab : a ≤ b) (heq : g a = g b) (s t : unitInterval) :
    pathOscillation (Icc s t) (erasePathLoop g a b hab heq) ≤ pathOscillation (Icc s t) g := by
  apply diam_le_of_forall_dist_le Metric.diam_nonneg
  rintro _ ⟨u, hu, rfl⟩ _ ⟨v, hv, rfl⟩
  wlog huv : u ≤ v generalizing u v
  · simpa only [dist_comm] using this v hv u hu (le_of_not_ge huv)
  rcases erasePathLoop_pair g hab heq huv with hsame | ⟨p, hp, q, hq, hup, hvq⟩
  · simpa only [hsame, dist_self] using (Metric.diam_nonneg (s := g '' Icc s t))
  · rw [hup, hvq]
    exact dist_le_diam_of_mem (path_image_isBounded (Icc s t) g)
      (mem_image_of_mem g ⟨hu.1.trans hp.1, hp.2.trans hv.2⟩)
      (mem_image_of_mem g ⟨hu.1.trans hq.1, hq.2.trans hv.2⟩)

lemma pathOscillation_erase_eq_zero (g : C(unitInterval, X))
    {a b s t : unitInterval} (hab : a ≤ b) (heq : g a = g b)
    (hs : a ≤ s) (ht : t ≤ b) :
    pathOscillation (Icc s t) (erasePathLoop g a b hab heq) = 0 := by
  apply le_antisymm _ Metric.diam_nonneg
  apply diam_le_of_forall_dist_le le_rfl
  rintro _ ⟨u, hu, rfl⟩ _ ⟨v, hv, rfl⟩
  rw [erasePathLoop_of_mem g hab heq ⟨hs.trans hu.1, hu.2.trans ht⟩,
    erasePathLoop_of_mem g hab heq ⟨hs.trans hv.1, hv.2.trans ht⟩, dist_self]

end CircleDomainRigidity

end

end OAI
