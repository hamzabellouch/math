import OAI.Combinatorics.Crossing.FiniteLineAvoidance
import OAI.Combinatorics.Crossing.SegmentSides

namespace OAI

noncomputable section
namespace Zarankiewicz

theorem exists_generic_point_extension {ι κ ν : Type*} [Fintype ι] [Fintype κ] [Fintype ν]
    (p : ι → Plane) (q : ν → Plane) (a v : κ → Plane)
    (hv : ∀ k, v k ≠ 0) (hpq : ∀ i j, q j ≠ p i)
    (z : Plane) (ε : ℝ) (hε : 0 < ε) :
    ∃ x : Plane, dist x z < ε ∧
      (∀ i, x ≠ p i) ∧ (∀ j, q j ≠ x) ∧
      (∀ k, det2 (x-a k) (v k) ≠ 0) ∧
      (∀ i k, det2 (x-p i) (v k) ≠ 0) ∧
      (∀ i j, orient2 (p i) x (q j) ≠ 0) := by
  let J := κ ⊕ (ν ⊕ (ι ⊕ ((ι × κ) ⊕ (ι × ν))))
  let base : J → Plane
    | .inl k => a k
    | .inr (.inl j) => q j
    | .inr (.inr (.inl i)) => p i
    | .inr (.inr (.inr (.inl (i,_)))) => p i
    | .inr (.inr (.inr (.inr (i,_)))) => p i
  let direction : J → Plane
    | .inl k => v k
    | .inr (.inl _) => (1,0)
    | .inr (.inr (.inl _)) => (1,0)
    | .inr (.inr (.inr (.inl (_,k)))) => v k
    | .inr (.inr (.inr (.inr (i,j)))) => q j-p i
  have hd : ∀ k, direction k ≠ 0 := by
    rintro (k|(j|(i|(⟨i,k⟩|⟨i,j⟩))))
    · exact hv k
    · norm_num [direction]
    · norm_num [direction]
    · exact hv k
    · exact sub_ne_zero.mpr (hpq i j)
  obtain ⟨x,hx,havoid⟩ := exists_near_avoiding_lines base direction hd z ε hε
  refine ⟨x,hx,?_,?_,?_,?_,?_⟩
  · intro i heq
    have hh := havoid (.inr (.inr (.inl i)))
    simp [base,direction,heq,det2] at hh
  · intro j heq
    have hh := havoid (.inr (.inl j))
    simp [base,direction,← heq,det2] at hh
  · intro k
    exact havoid (.inl k)
  · intro i k
    exact havoid (.inr (.inr (.inr (.inl (i,k)))))
  · intro i j
    exact havoid (.inr (.inr (.inr (.inr (i,j)))))

end Zarankiewicz

end

end OAI
