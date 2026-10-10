import OAI.MeasureTheory.Falconer.Geometry.DyadicSeparation
import OAI.MeasureTheory.Falconer.Estimates.DyadicAncestors
import OAI.MeasureTheory.Falconer.Estimates.PrefixCounting

namespace OAI

/-! Real coordinates of the scalar dyadic tree used in the initial
 regularization. These are the existing geometric descendants. -/
namespace Falconer

noncomputable def scalarPathCenter (p : List (Fin 1 → Bool)) : ℝ :=
  ((⟨0,1⟩ : DyadicCube 1).descendant p).center 0

 theorem scalar_space_dist (x y : Space 1) : dist x y = |x 0-y 0| := by
  rw [PiLp.dist_eq_of_L2]
  simp [Real.dist_eq,Real.sqrt_sq_eq_abs]

 theorem scalarPathCenter_separated {b : ℕ} {p q : List (Fin 1 → Bool)}
    (hp : p.length = b) (hq : q.length = b) (hne : p ≠ q) :
    (1/2:ℝ)^b ≤ |scalarPathCenter p-scalarPathCenter q| := by
  have hh := (⟨0,1⟩ : DyadicCube 1).centers_separated (by norm_num) hp hq hne
  simpa only [scalar_space_dist,scalarPathCenter,div_pow,one_pow] using hh

 theorem scalarPathCenter_injOn {b : ℕ} (C : Finset (List (Fin 1 → Bool)))
    (hlen : ∀ p ∈ C, p.length = b) : Set.InjOn scalarPathCenter (C : Set (List (Fin 1 → Bool))) := by
  intro p hp q hq heq
  by_contra hne
  have hh := scalarPathCenter_separated (hlen p hp) (hlen q hq) hne
  rw [heq,sub_self,abs_zero] at hh
  exact (not_le_of_gt (pow_pos (by norm_num : (0:ℝ) < 1/2) b)) hh

 theorem scalarPathCenter_same_parent {a b : ℕ} {p q : List (Fin 1 → Bool)}
    (hp : p.length = b) (hab : a ≤ b) (heq : p.take a = q.take a) :
    |scalarPathCenter p-scalarPathCenter q| ≤ (1/2:ℝ)^a := by
  have hh := (⟨0,1⟩ : DyadicCube 1).same_ancestor_center_dist (by norm_num) p q hp hab heq
  simpa only [scalar_space_dist,scalarPathCenter,Nat.cast_one,Real.sqrt_one,one_mul,
    div_pow,one_pow] using hh

namespace Regularization

 theorem scalar_prefix_children_length {N a b : ℕ} {L : Finset (CellPath 1)}
    (hL : L ⊆ cubePaths 1 N) (hb : b ≤ N) (p : CellPath 1) :
    ∀ q ∈ prefixChildren L a b p, q.length = b := by
  classical
  intro q hq
  obtain ⟨r,hr,rfl⟩ := Finset.mem_image.mp hq
  have hrN := (mem_cubePaths 1 N r).mp (hL (Finset.mem_filter.mp hr).1)
  simp only [List.length_take,hrN,min_eq_left hb]

 theorem scalar_prefix_children_parent {a b : ℕ} (hab : a ≤ b)
    (L : Finset (CellPath 1)) (p : CellPath 1) :
    ∀ q ∈ prefixChildren L a b p, q.take a = p := by
  classical
  intro q hq
  obtain ⟨r,hr,rfl⟩ := Finset.mem_image.mp hq
  rw [List.take_take,min_eq_left hab]
  exact (Finset.mem_filter.mp hr).2

end Regularization
end Falconer

end OAI
