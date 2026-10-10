import Mathlib
import OAI.GroupTheory.SimpleAmenable.PolygonGeometry.WindowRectangles

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section UniformConcurrentMesh

noncomputable def lineIntersectionCoefficient (a : ℕ) (i j : Fin 4) : ℝ :=
  ((|ordinary (lineNormal a i).1|+|ordinary (lineNormal a i).2|+
      |ordinary (lineNormal a j).1|+|ordinary (lineNormal a j).2|)/
      |ordinary (lineDet a i j)|)*
    max (|ordinary (lineNormal a i).1|+|ordinary (lineNormal a i).2|)
      (|ordinary (lineNormal a j).1|+|ordinary (lineNormal a j).2|)

noncomputable def lineIntersectionConstant (a : ℕ) : ℝ :=
  1+∑ i : Fin 4, ∑ j : Fin 4, lineIntersectionCoefficient a i j

theorem lineIntersectionCoefficient_nonneg (a : ℕ) (i j : Fin 4) :
    0≤lineIntersectionCoefficient a i j := by
  unfold lineIntersectionCoefficient
  positivity

theorem lineIntersectionConstant_ge_one (a : ℕ) : 1≤lineIntersectionConstant a := by
  unfold lineIntersectionConstant
  have h : 0≤∑ i : Fin 4, ∑ j : Fin 4, lineIntersectionCoefficient a i j :=
    Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => lineIntersectionCoefficient_nonneg a i j))
  linarith

theorem lineIntersectionCoefficient_le (a : ℕ) (i j : Fin 4) :
    lineIntersectionCoefficient a i j≤lineIntersectionConstant a := by
  have h₁ := Finset.single_le_sum (fun k (_ : k ∈ (Finset.univ : Finset (Fin 4))) =>
    lineIntersectionCoefficient_nonneg a i k) (Finset.mem_univ j)
  have h₂ := Finset.single_le_sum (fun k (_ : k ∈ (Finset.univ : Finset (Fin 4))) =>
    Finset.sum_nonneg (fun l (_ : l ∈ (Finset.univ : Finset (Fin 4))) =>
      lineIntersectionCoefficient_nonneg a k l)) (Finset.mem_univ i)
  unfold lineIntersectionConstant
  linarith

theorem exists_uniform_concurrent_mesh (a : ℕ) (r : CutRing) (ε : ℝ) (hε : 0<ε) :
    ∃ n : ℕ, 201≤n ∧ symmetricWindowLength r≤n ∧
      200/(n:ℝ)<ε ∧
      ∀ i j : Fin 4, lineIntersectionCoefficient a i j*(200/(n:ℝ))<ε := by
  obtain ⟨N,hN⟩ := exists_nat_gt (200*lineIntersectionConstant a/ε)
  let n := max 201 (max N (symmetricWindowLength r))
  have hn : 201≤n := le_max_left _ _
  have hNN : N≤n := (le_max_left _ _).trans (le_max_right _ _)
  have hn' : 0<(n:ℝ) := by exact_mod_cast (show 0<n by omega)
  have hlarge : 200*lineIntersectionConstant a<ε*(n:ℝ) := by
    have h := (div_lt_iff₀ hε).mp hN
    have hcast : (N:ℝ)≤(n:ℝ) := by exact_mod_cast hNN
    nlinarith
  have hC := lineIntersectionConstant_ge_one a
  have hsmall : lineIntersectionConstant a*(200/(n:ℝ))<ε := by
    rw [← mul_div_assoc,div_lt_iff₀ hn']
    nlinarith
  refine ⟨n,hn,(le_max_right _ _).trans (le_max_right _ _),?_,?_⟩
  · have hm := mul_le_mul_of_nonneg_right hC (show 0≤200/(n:ℝ) by positivity)
    simpa only [one_mul] using hm.trans_lt hsmall
  · intro i j
    exact (mul_le_mul_of_nonneg_right (lineIntersectionCoefficient_le a i j)
      (show 0≤200/(n:ℝ) by positivity)).trans_lt hsmall

theorem windowRectangle_concurrent_uniform {a : ℕ} (ha : 0<a)
    (n : ℕ) (hn : 201≤n) (q : Fin 2 → ℤ) (cell : Fin 2 → Fin n)
    (i j : Fin 4) (hij : i≠j) (c d : CutRing)
    (p x y u v : GenericSquare a)
    (hp : p ∈ (windowRectangle a n q cell).val)
    (hx : x ∈ (windowRectangle a n q cell).val)
    (hy : y ∈ (windowRectangle a n q cell).val)
    (hu : u ∈ (windowRectangle a n q cell).val)
    (hv : v ∈ (windowRectangle a n q cell).val)
    (hcx : cutForm a i (windowPlanarLift q x)≤ordinary c)
    (hcy : ordinary c≤cutForm a i (windowPlanarLift q y))
    (hdu : cutForm a j (windowPlanarLift q u)≤ordinary d)
    (hdv : ordinary d≤cutForm a j (windowPlanarLift q v)) :
    ∃ z : ℝ × ℝ, cutForm a i z=ordinary c ∧ cutForm a j z=ordinary d ∧
      dist z (windowPlanarLift q p)≤lineIntersectionConstant a*(200/(n:ℝ)) := by
  obtain ⟨z,hi,hj,hb⟩ := windowRectangle_intersection_near ha n hn q cell i j hij c d
    p x y u v hp hx hy hu hv hcx hcy hdu hdv
  refine ⟨z,hi,hj,hb.trans ?_⟩
  rw [← mul_assoc]
  exact mul_le_mul_of_nonneg_right (lineIntersectionCoefficient_le a i j) (by positivity)

end UniformConcurrentMesh

end SimpleAmenable
end
end

end OAI
