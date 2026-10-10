import OAI.Combinatorics.Crossing.FiniteLineAvoidance
import OAI.Combinatorics.Crossing.TriangleOrientations

namespace OAI

noncomputable section
namespace Zarankiewicz

theorem exists_polygon_cone_point (v w : ℕ → Plane) (n m : ℕ)
    (hv : ∀ i : Fin n, v (i.val+1) ≠ v i.val)
    (hw : ∀ j : Fin m, w (j.val+1) ≠ w j.val)
    (hvw : ∀ i : Fin (n+1), ∀ j : Fin (m+1), w j.val ≠ v i.val) :
    ∃ o : Plane,
      (∀ i : Fin n, orient2 o (v i.val) (v (i.val+1)) ≠ 0) ∧
      (∀ j : Fin m, orient2 (w j.val) (w (j.val+1)) o ≠ 0) ∧
      (∀ i : Fin (n+1), ∀ j : Fin m, det2 (v i.val-o) (w (j.val+1)-w j.val) ≠ 0) ∧
      (∀ i : Fin (n+1), ∀ j : Fin (m+1), orient2 o (v i.val) (w j.val) ≠ 0) := by
  let ι := (Fin n ⊕ Fin m) ⊕ ((Fin (n+1) × Fin m) ⊕ (Fin (n+1) × Fin (m+1)))
  let base : ι → Plane
    | .inl (.inl i) => v i.val
    | .inl (.inr j) => w j.val
    | .inr (.inl (i,_)) => v i.val
    | .inr (.inr (i,_)) => v i.val
  let direction : ι → Plane
    | .inl (.inl i) => v (i.val+1)-v i.val
    | .inl (.inr j) => w (j.val+1)-w j.val
    | .inr (.inl (_,j)) => w (j.val+1)-w j.val
    | .inr (.inr (i,j)) => w j.val-v i.val
  have hd : ∀ k, direction k ≠ 0 := by
    rintro ((i|j)|(⟨i,j⟩|⟨i,j⟩))
    · exact sub_ne_zero.mpr (hv i)
    · exact sub_ne_zero.mpr (hw j)
    · exact sub_ne_zero.mpr (hw j)
    · exact sub_ne_zero.mpr (hvw i j)
  obtain ⟨o,_,ho⟩ := exists_near_avoiding_lines base direction hd (0 : Plane) 1 (by norm_num)
  refine ⟨o,?_,?_,?_,?_⟩
  · intro i
    rw [← triangle_area_cycle o (v i.val) (v (i.val+1))]
    change det2 (v (i.val+1)-v i.val) (o-v i.val) ≠ 0
    rw [det2_swap]
    exact neg_ne_zero.mpr (ho (.inl (.inl i)))
  · intro j
    change det2 (w (j.val+1)-w j.val) (o-w j.val) ≠ 0
    rw [det2_swap]
    exact neg_ne_zero.mpr (ho (.inl (.inr j)))
  · intro i j
    rw [det2_reverse_edge (v i.val) o (w j.val) (w (j.val+1))]
    exact neg_ne_zero.mpr (ho (.inr (.inl (i,j))))
  · intro i j
    rw [← triangle_area_cycle o (v i.val) (w j.val)]
    change det2 (w j.val-v i.val) (o-v i.val) ≠ 0
    rw [det2_swap]
    exact neg_ne_zero.mpr (ho (.inr (.inr (i,j))))

end Zarankiewicz

end

end OAI
