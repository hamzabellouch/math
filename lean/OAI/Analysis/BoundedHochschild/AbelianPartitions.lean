import Mathlib

namespace OAI

/-!
# Common finite partitions for commuting projections

A finite family of projections in a commutative C⋆-algebra admits a common
orthogonal partition of unity. Adjoining one projection refines every cell
by multiplication with that projection and its complement. Zero cells are
retained, so no nonzero or trace assumptions are needed.
-/

noncomputable section

namespace BoundedHochschild
namespace KadisonRingrose

open scoped BigOperators

variable {M : Type*} [CommCStarAlgebra M]

private lemma split_same (a b q : M) (hq : IsStarProjection q) :
    (a * q) * (b * q) = (a * b) * q := by
  calc
    (a * q) * (b * q) = (a * b) * (q * q) := by ring
    _ = (a * b) * q := by rw [hq.isIdempotentElem.eq]

private lemma split_cross (a b q : M) (hq : IsStarProjection q) :
    (a * q) * (b * (1 - q)) = 0 := by
  have hzero : q * (1 - q) = 0 := by
    rw [mul_sub, mul_one, hq.isIdempotentElem.eq, sub_self]
  calc
    (a * q) * (b * (1 - q)) = (a * b) * (q * (1 - q)) := by ring
    _ = 0 := by rw [hzero, mul_zero]

private lemma decides_mul {r a : M} (h : r * a = 0 ∨ r * a = a) (b : M) :
    r * (a * b) = 0 ∨ r * (a * b) = a * b := by
  rcases h with h | h
  · exact Or.inl (by rw [← mul_assoc, h, zero_mul])
  · exact Or.inr (by rw [← mul_assoc, h])

/-- A common orthogonal partition of unity for any finite family of projections. -/
theorem exists_refining_partition (S : Finset {q : M // IsStarProjection q}) :
    ∃ (n : ℕ) (p : Fin n → M),
      (∀ i, IsStarProjection (p i)) ∧
      (∀ i j, i ≠ j → p i * p j = 0) ∧
      (∑ i, p i) = 1 ∧
      (∀ q ∈ S, ∀ i, q.val * p i = 0 ∨ q.val * p i = p i) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    refine ⟨1, fun _ => 1, fun _ => IsStarProjection.one M, ?_, by simp, ?_⟩
    · intro i j hij
      exact (hij (Subsingleton.elim i j)).elim
    · simp
  | @insert q S _ ih =>
    obtain ⟨n, p, hp, ho, hsum, hdec⟩ := ih
    let parts : Fin (n + n) → M :=
      Fin.append (fun i => p i * q.val) (fun i => p i * (1 - q.val))
    refine ⟨n + n, parts, ?_, ?_, ?_, ?_⟩
    · intro i
      refine Fin.addCases (fun j => ?_) (fun j => ?_) i
      · simpa only [parts, Fin.append_left] using (hp j).mul q.property (Commute.all _ _)
      · simpa only [parts, Fin.append_right] using
          (hp j).mul q.property.one_sub (Commute.all _ _)
    · intro i j
      refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;>
        refine Fin.addCases (fun j => ?_) (fun j => ?_) j <;> intro hij
      · have hij' : i ≠ j := fun h => hij (congrArg (Fin.castAdd n) h)
        simp only [parts, Fin.append_left]
        change (p i * q.val) * (p j * q.val) = 0
        rw [split_same _ _ _ q.property, ho i j hij', zero_mul]
      · simp only [parts, Fin.append_left, Fin.append_right]
        exact split_cross _ _ _ q.property
      · simp only [parts, Fin.append_left, Fin.append_right]
        rw [mul_comm]
        exact split_cross _ _ _ q.property
      · have hij' : i ≠ j := fun h => hij (congrArg (Fin.natAdd n) h)
        simp only [parts, Fin.append_right]
        change (p i * (1 - q.val)) * (p j * (1 - q.val)) = 0
        rw [split_same _ _ _ q.property.one_sub, ho i j hij', zero_mul]
    · simp only [parts, Fin.sum_univ_add, Fin.append_left, Fin.append_right]
      rw [← Finset.sum_mul, ← Finset.sum_mul, hsum]
      ring
    · intro r hr i
      rcases Finset.mem_insert.mp hr with hrq | hr
      · subst r
        refine Fin.addCases (fun j => ?_) (fun j => ?_) i
        · simp only [parts, Fin.append_left]
          right
          calc
            q.val * (p j * q.val) = p j * (q.val * q.val) := by ring
            _ = p j * q.val := by rw [q.property.isIdempotentElem.eq]
        · simp only [parts, Fin.append_right]
          left
          calc
            q.val * (p j * (1 - q.val)) = p j * (q.val * (1 - q.val)) := by ring
            _ = 0 := by rw [mul_sub, mul_one, q.property.isIdempotentElem.eq, sub_self, mul_zero]
      · refine Fin.addCases (fun j => ?_) (fun j => ?_) i
        · simpa only [parts, Fin.append_left] using decides_mul (hdec r hr j) q.val
        · simpa only [parts, Fin.append_right] using decides_mul (hdec r hr j) (1 - q.val)

end KadisonRingrose
end BoundedHochschild

end

end OAI
