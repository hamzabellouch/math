import OAI.Analysis.SphereIsometry.BarycentricBasic
import Mathlib.Data.Finset.Union
import OAI.Analysis.SphereIsometry.ProbabilitySimplex

namespace OAI

/-!
# Supports of finite barycenters

A nonempty average of simplex vectors is a simplex vector. Its strict-positive
coordinate support is exactly the union of the supports being averaged.
These statements concern the actual finite average and require no geometric
coverage assumption.
-/

noncomputable section

open scoped BigOperators Classical

namespace Tingley

variable {V ι : Type*} [Fintype ι]

/-- The coordinates at which a vector is strictly positive. -/
def positiveCarrier (x : ι → ℝ) : Finset ι :=
  Finset.univ.filter (fun i => 0 < x i)

@[simp] theorem mem_positiveCarrier {x : ι → ℝ} {i : ι} :
    i ∈ positiveCarrier x ↔ 0 < x i := by
  simp [positiveCarrier]

/-- Outside the positive carrier, a nonnegative vector has zero coordinates. -/
theorem not_mem_positiveCarrier_iff {x : ι → ℝ} (hx : ∀ i, 0 ≤ x i) (i : ι) :
    i ∉ positiveCarrier x ↔ x i = 0 := by
  rw [mem_positiveCarrier, not_lt]
  exact ⟨fun h => le_antisymm h (hx i), fun h => h.le⟩

/-- Containment in a coordinate face is exactly vanishing outside that face. -/
theorem positiveCarrier_subset_iff {x : ι → ℝ} (hx : ∀ i, 0 ≤ x i)
    (I : Finset ι) :
    positiveCarrier x ⊆ I ↔ ∀ i, i ∉ I → x i = 0 := by
  constructor
  · intro h i hi
    apply (not_mem_positiveCarrier_iff hx i).mp
    intro hix
    exact hi (h hix)
  · intro h i hi
    by_contra hn
    have hzero := h i hn
    have hpos := mem_positiveCarrier.mp hi
    rw [hzero] at hpos
    exact (lt_irrefl (0 : ℝ)) hpos

/-- Finite averaging preserves nonnegative coordinates, including for the empty set. -/
theorem finiteBarycenter_apply_nonneg (p : V → ι → ℝ) (S : Finset V)
    (hp : ∀ v ∈ S, ∀ i, 0 ≤ p v i) (i : ι) :
    0 ≤ finiteBarycenter p S i := by
  rw [finiteBarycenter_apply]
  exact mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg S.card))
    (Finset.sum_nonneg (fun v hv => hp v hv i))

/-- A nonempty finite average stays in the standard simplex. -/
theorem finiteBarycenter_mem_stdSimplex (p : V → ι → ℝ) {S : Finset V}
    (hs : S.Nonempty) (hp : ∀ v ∈ S, p v ∈ probabilitySimplexSet ι) :
    finiteBarycenter p S ∈ probabilitySimplexSet ι := by
  exact finiteBarycenter_mem_convex (convex_probabilitySimplexSet ι) hs hp

/-- A coordinate of a nonempty nonnegative average is positive exactly when
one of the averaged coordinates is positive. -/
theorem finiteBarycenter_pos_iff (p : V → ι → ℝ) {S : Finset V}
    (hs : S.Nonempty) (hp : ∀ v ∈ S, ∀ i, 0 ≤ p v i) (i : ι) :
    0 < finiteBarycenter p S i ↔ ∃ v ∈ S, 0 < p v i := by
  have hcard : 0 < (S.card : ℝ) := Nat.cast_pos.mpr (Finset.card_pos.mpr hs)
  have hinv : 0 < (S.card : ℝ)⁻¹ := inv_pos.mpr hcard
  rw [finiteBarycenter_apply]
  constructor
  · intro h
    have hsum : 0 < ∑ v ∈ S, p v i := pos_of_mul_pos_right h hinv.le
    by_contra hn
    have hzero : ∀ v ∈ S, p v i = 0 := by
      intro v hv
      apply le_antisymm _ (hp v hv i)
      exact le_of_not_gt (fun hpos => hn ⟨v, hv, hpos⟩)
    have heq : ∑ v ∈ S, p v i = 0 := Finset.sum_eq_zero hzero
    rw [heq] at hsum
    exact (lt_irrefl (0 : ℝ)) hsum
  · intro h
    exact mul_pos hinv (Finset.sum_pos' (fun v hv => hp v hv i) h)

/-- The support of a nonempty nonnegative average is the exact support union. -/
theorem positiveCarrier_finiteBarycenter (p : V → ι → ℝ) {S : Finset V}
    (hs : S.Nonempty) (hp : ∀ v ∈ S, ∀ i, 0 ≤ p v i) :
    positiveCarrier (finiteBarycenter p S) =
      S.biUnion (fun v => positiveCarrier (p v)) := by
  ext i
  simp only [mem_positiveCarrier, Finset.mem_biUnion]
  exact finiteBarycenter_pos_iff p hs hp i

/-- The new vertex belongs to an original coordinate face exactly when every
averaged vertex belongs to that face. -/
theorem positiveCarrier_finiteBarycenter_subset_iff (p : V → ι → ℝ)
    {S : Finset V} (hs : S.Nonempty) (hp : ∀ v ∈ S, ∀ i, 0 ≤ p v i)
    (I : Finset ι) :
    positiveCarrier (finiteBarycenter p S) ⊆ I ↔
      ∀ v ∈ S, positiveCarrier (p v) ⊆ I := by
  rw [positiveCarrier_finiteBarycenter p hs hp]
  exact Finset.biUnion_subset

/-- A simplex vector has a positive coordinate because its total mass is one. -/
theorem positiveCarrier_nonempty_of_mem_stdSimplex {x : ι → ℝ}
    (hx : x ∈ probabilitySimplexSet ι) : (positiveCarrier x).Nonempty := by
  by_contra hn
  have hzero : ∀ i, x i = 0 := by
    intro i
    apply le_antisymm _ (hx.1 i)
    exact le_of_not_gt (fun hpos => hn ⟨i, mem_positiveCarrier.mpr hpos⟩)
  have hsum : ∑ i, x i = 0 := Finset.sum_eq_zero (fun i _ => hzero i)
  exact one_ne_zero (hx.2.symm.trans hsum)

end Tingley

end

end OAI
