import OAI.Analysis.KadisonSimilarity.Representation.DenseStarRepresentation
import Mathlib.SetTheory.Cardinal.Free

namespace OAI

/-! # Countable dense star subrings

A separable complex C-star algebra has a countable norm-dense subring,
closed under star and containing the scalar `i`. This supplies the domain
on which countably many almost-everywhere algebra identities suffice.
-/

noncomputable section
namespace KadisonSimilarity

open scoped Topology Pointwise

theorem countable_subringClosure {R : Type*} [Ring R] {s : Set R}
    (hs : s.Countable) : (Subring.closure s : Set R).Countable := by
  let : Countable s := hs.to_subtype
  let f : FreeRing s →+* R := FreeRing.lift (fun x : s => (x : R))
  have hle : Subring.closure s ≤ f.range := Subring.closure_le.mpr fun x hx => by
    exact ⟨FreeRing.of ⟨x, hx⟩, FreeRing.lift_of _ _⟩
  exact (Set.countable_range f).mono hle

theorem star_mem_subringClosure_union {R : Type*} [Ring R] [StarRing R]
    (s : Set R) {x : R} (hx : x ∈ Subring.closure (s ∪ star s)) :
    star x ∈ Subring.closure (s ∪ star s) := by
  induction hx using Subring.closure_induction with
  | mem x hx =>
      apply Subring.subset_closure
      rcases hx with hx | hx
      · exact Or.inr (Set.star_mem_star.mpr hx)
      · exact Or.inl (Set.mem_star.mp hx)
  | zero => simpa only [star_zero] using (Subring.closure (s ∪ star s)).zero_mem
  | one => simpa only [star_one] using (Subring.closure (s ∪ star s)).one_mem
  | add x y _ _ hx hy => simpa only [star_add] using add_mem hx hy
  | neg x _ hx => simpa only [star_neg] using neg_mem hx
  | mul x y _ _ hx hy => simpa only [star_mul] using mul_mem hy hx

/-- A concrete countable domain for gathering the pointwise fiber laws. -/
theorem exists_countable_dense_star_subring (A : Type*) [CStarAlgebra A]
    [TopologicalSpace.SeparableSpace A] :
    ∃ S : Subring A, (S : Set A).Countable ∧ Dense (S : Set A) ∧
      (∀ a ∈ S, star a ∈ S) ∧ algebraMap ℂ A Complex.I ∈ S := by
  let s : Set A := Set.range (TopologicalSpace.denseSeq A) ∪
    {algebraMap ℂ A Complex.I}
  let S := Subring.closure (s ∪ star s)
  have hs : s.Countable := (Set.countable_range _).union (Set.countable_singleton _)
  have hstar : (star s).Countable := by
    rw [← Set.image_star]
    exact hs.image star
  refine ⟨S, countable_subringClosure (hs.union hstar), ?_, ?_, ?_⟩
  · exact (TopologicalSpace.denseRange_denseSeq A).mono fun a ha =>
      Subring.subset_closure (Or.inl (Or.inl ha))
  · exact fun a ha => star_mem_subringClosure_union s ha
  · exact Subring.subset_closure (Or.inl (Or.inr (Set.mem_singleton _)))

end KadisonSimilarity

end

end OAI
