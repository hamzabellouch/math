import Mathlib

namespace OAI

section
section
section
noncomputable section
namespace CannonConvexRetraction
open Set
open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem exists_retraction (K : Set E) (hne : K.Nonempty) (hc : IsClosed K)
    (hconv : Convex ℝ K) :
    ∃ P : E → E,LipschitzWith 1 P ∧ (∀ x,P x∈K) ∧ ∀ x∈K,P x=x := by
  have hex (x : E) := exists_norm_eq_iInf_of_complete_convex hne hc.isComplete hconv x
  choose P hP hmin using hex
  have hinner (x w : E) (hw : w∈K) : ⟪x-P x,w-P x⟫_ℝ≤0 :=
    (norm_eq_iInf_iff_real_inner_le_zero hconv (hP x)).mp (hmin x) w hw
  have hdist (x y : E) : dist (P x) (P y)≤dist x y := by
    have hx := hinner x (P y) (hP y)
    have hy := hinner y (P x) (hP x)
    have hh : ‖P x-P y‖^2≤⟪x-y,P x-P y⟫_ℝ := by
      rw [←real_inner_self_eq_norm_sq]
      simp only [inner_sub_left,inner_sub_right] at hx hy ⊢
      have hs := real_inner_comm (P x) (P y)
      linarith
    have hcs := real_inner_le_norm (x-y) (P x-P y)
    rw [dist_eq_norm,dist_eq_norm]
    by_cases hz : ‖P x-P y‖=0
    · rw [hz]; exact norm_nonneg _
    · have hp : 0<‖P x-P y‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)
      nlinarith
  refine ⟨P,LipschitzWith.of_dist_le_mul (by simpa using hdist),hP,?_⟩
  intro x hx
  have H := hinner x x hx
  rw [real_inner_self_eq_norm_sq] at H
  have hzero : ‖x-P x‖=0 := by nlinarith [norm_nonneg (x-P x)]
  exact (sub_eq_zero.mp (norm_eq_zero.mp hzero)).symm
end CannonConvexRetraction

end
end
section
noncomputable section
namespace CannonFiniteClosedGluing
open Set

variable {X Y D : Type*} [TopologicalSpace X] [TopologicalSpace Y] [Finite D]

theorem exists_gluing (C : D → Set X) (hC : ∀ d,IsClosed (C d))
    (hcover : ∀ x,∃ d,x∈C d) (f : D → ContinuousMap X Y)
    (hcompat : ∀ d e x,x∈C d → x∈C e → f d x=f e x) :
    ∃ g : ContinuousMap X Y,∀ d x,x∈C d → g x=f d x := by
  choose ind hind using hcover
  let g : X → Y := fun x=>f (ind x) x
  have heq (d : D) (x : X) (hx : x∈C d) : g x=f d x :=
    hcompat (ind x) d x (hind x) hx
  have hcont : Continuous g := by
    rw [continuous_iff_isClosed]
    intro S hS
    have hpre : g ⁻¹' S=⋃ d,C d∩(f d) ⁻¹' S := by
      ext x
      simp only [mem_preimage,mem_iUnion,mem_inter_iff]
      constructor
      · intro hx
        exact ⟨ind x,hind x,hx⟩
      · rintro ⟨d,hd,hx⟩
        rwa [heq d x hd]
    rw [hpre]
    exact isClosed_iUnion_of_finite fun d=>(hC d).inter (hS.preimage (f d).continuous)
  exact ⟨⟨g,hcont⟩,heq⟩
end CannonFiniteClosedGluing

end
end
end
end

end OAI
