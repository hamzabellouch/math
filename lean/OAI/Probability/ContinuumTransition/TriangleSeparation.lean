import OAI.Probability.ContinuumTransition.FreeIdeal

namespace OAI

section
open scoped Topology
open Set Filter Metric
noncomputable section
namespace ContinuumTemperature

def vertexCoordinate (p : ℝ) (z : Parameter) (i : Fin 3) : ℝ :=
  if i = 0 then 1+(12*z.1-45*z.2)/(36*p)
  else if i = 1 then (12*z.2-4*z.1)/(9*p)
  else (4*z.1-3*z.2)/(36*p)

lemma vertexCoordinate_center {p : ℝ} (hp : 0 < p) (i : Fin 3) :
    vertexCoordinate p (triangleCenter p) i = 1/3 := by
  fin_cases i <;> norm_num [vertexCoordinate,triangleCenter]
  all_goals field_simp [hp.ne']; ring

lemma vertexCoordinate_affine (p a b : ℝ) (hab : a+b=1) (x y : Parameter) (i : Fin 3) :
    vertexCoordinate p (a • x+b • y) i = a*vertexCoordinate p x i+b*vertexCoordinate p y i := by
  fin_cases i <;> simp [vertexCoordinate]
  · linear_combination -hab
  · ring
  · ring

lemma vertex_halfspace_convex (p c : ℝ) (i : Fin 3) :
    Convex ℝ {z | vertexCoordinate p z i ≤ c} := by
  intro x hx y hy a b ha hb hab
  change vertexCoordinate p (a • x+b • y) i ≤ c
  rw [vertexCoordinate_affine p a b hab]
  exact (add_le_add (mul_le_mul_of_nonneg_left hx ha) (mul_le_mul_of_nonneg_left hy hb)).trans_eq (by rw [← add_mul,hab,one_mul])

lemma coordinates_of_near_vertex {p τ : ℝ} {i : Fin 3} {w : Parameter}
    (hw : w ∈ closedBall (triangleVertex p i) τ) :
    |w.1-(triangleVertex p i).1| ≤ τ ∧ |w.2-(triangleVertex p i).2| ≤ τ := by
  simpa only [mem_closedBall,dist_eq_norm_sub,Prod.norm_def,Prod.fst_sub,Prod.snd_sub,
    Real.norm_eq_abs,max_le_iff] using hw

lemma vertexCoordinate_near_other {p τ : ℝ} (hp : 0 < p) (hτ : τ ≤ p/100)
    {i j : Fin 3} (hij : i ≠ j) {w : Parameter}
    (hw : w ∈ closedBall (triangleVertex p j) τ) : vertexCoordinate p w i ≤ 1/6 := by
  obtain ⟨h1,h2⟩ := coordinates_of_near_vertex hw
  obtain ⟨hl1,hu1⟩ := abs_le.mp h1
  obtain ⟨hl2,hu2⟩ := abs_le.mp h2
  apply (mul_le_mul_iff_right₀ hp).mp
  fin_cases i <;> fin_cases j <;> norm_num [vertexCoordinate,triangleVertex] at hl1 hu1 hl2 hu2 ⊢
  all_goals try contradiction
  all_goals field_simp [hp.ne']; nlinarith only [hl1,hu1,hl2,hu2,hτ,hp]

lemma vertex_density_separation {p τ : ℝ} (hp : 0 < p) (hτ : τ ≤ p/100)
    {i j : Fin 3} (hij : i ≠ j) :
    Disjoint (Prod.snd '' closedBall (triangleVertex p i) τ)
      (Prod.snd '' closedBall (triangleVertex p j) τ) := by
  apply Set.disjoint_left.mpr
  rintro d ⟨w,hw,rfl⟩ ⟨z,hz,he⟩
  have hw' := (coordinates_of_near_vertex hw).2
  have hz' := (coordinates_of_near_vertex hz).2
  obtain ⟨hw1,hw2⟩ := abs_le.mp hw'
  obtain ⟨hz1,hz2⟩ := abs_le.mp hz'
  fin_cases i <;> fin_cases j <;> norm_num [triangleVertex] at hw1 hw2 hz1 hz2
  all_goals try contradiction
  all_goals linarith only [hw1,hw2,hz1,hz2,he,hτ,hp]

lemma all_vertex_groups_nonempty {p τ : ℝ} (hp : 0 < p) (hτ : τ ≤ p/100)
    (K : Fin 3 → Set Parameter) (hk : ∀ i, K i ⊆ closedBall (triangleVertex p i) τ)
    (hg : triangleCenter p ∈ convexHull ℝ (⋃ i, K i)) : ∀ i, (K i).Nonempty := by
  intro i
  by_contra hn
  have hs : (⋃ j, K j) ⊆ {z | vertexCoordinate p z i ≤ 1/6} := by
    rintro z ⟨_,⟨j,rfl⟩,hz⟩
    have hji : i ≠ j := by intro he; subst j; exact hn ⟨z,hz⟩
    exact vertexCoordinate_near_other hp hτ hji (hk j hz)
  have hh := convexHull_min hs (vertex_halfspace_convex p (1/6) i) hg
  change vertexCoordinate p (triangleCenter p) i ≤ 1/6 at hh
  rw [vertexCoordinate_center hp] at hh
  norm_num at hh

end ContinuumTemperature
end
end

end OAI
