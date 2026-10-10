import Mathlib
import OAI.Probability.LatticeSurface.Convexity.ElementaryKernels

namespace OAI

namespace ProjectionComparison

open Set ClusterDisplacement

variable {V E : Type*} [Fintype V] [Fintype E]

theorem tail_projection_kernel (S : System V E) (b₀ b₁ v₀ v₁ h₀ h₁ : V → ℝ) (a : ℝ)
    (hp₀ : IsProjection S b₀ v₀ h₀) (hp₁ : IsProjection S b₁ v₁ h₁)
    (hb : ∀x∈S.pins,b₁ x-b₀ x≤a) :
    ∃ A : Kernel V,Firm A ∧ ∃ r : V → ℝ,(∀x,r x∈Icc (0:ℝ) 1) ∧
      ∀x,max (h₁ x-h₀ x-a) 0=r x*A.apply (fun y => max (v₁ y-v₀ y-a) 0) x := by
  classical
  let u : V → ℝ := fun y => max (v₁ y-v₀ y-a) 0
  let v : V → ℝ := fun y => v₀ y+u y
  let hne : (feasible S b₀).Nonempty := ⟨h₀,hp₀.1⟩
  let k := project S b₀ hne v
  have hpk : IsProjection S b₀ v k := project_spec S b₀ hne v
  obtain ⟨A,hA,heq⟩:=projection_update_kernel S b₀ v₀ v h₀ k hp₀ hpk
  have he (x) : A.apply u x=k x-h₀ x := by
    simpa only [v,add_sub_cancel_left] using congrFun heq x
  have horder : ∀x,h₁ x≤k x+a := projection_order S b₁ b₀ v₁ v h₁ k a hp₁ hpk
    (fun x hx => by linarith [hb x hx])
    (fun x hx => by dsimp [v,u];linarith [le_max_left (v₁ x-v₀ x-a) 0])
  have hnn (x) : 0≤A.apply u x := Finset.sum_nonneg fun y _ => mul_nonneg (A.nonneg x y) (le_max_right _ _)
  have hle (x) : max (h₁ x-h₀ x-a) 0≤A.apply u x := by
    apply max_le
    · rw [he];linarith [horder x]
    · exact hnn x
  let r : V → ℝ := fun x => max (h₁ x-h₀ x-a) 0/A.apply u x
  refine ⟨A,hA,r,?_,?_⟩
  · intro x
    constructor
    · exact div_nonneg (le_max_right _ _) (hnn x)
    · by_cases hz : A.apply u x=0
      · simp [r,hz]
      · exact (div_le_one (lt_of_le_of_ne (hnn x) (Ne.symm hz))).mpr (hle x)
  · intro x
    by_cases hz : A.apply u x=0
    · have hu : max (h₁ x-h₀ x-a) 0=0 := le_antisymm (by simpa only [hz] using hle x) (le_max_right _ _)
      simp only [hu,r,zero_div,zero_mul]
    · exact (div_mul_cancel₀ _ hz).symm

end ProjectionComparison

end OAI
