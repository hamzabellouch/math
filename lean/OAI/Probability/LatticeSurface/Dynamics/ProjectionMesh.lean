import Mathlib
import OAI.Probability.LatticeSurface.Convexity.KernelRestriction
import OAI.Probability.LatticeSurface.Dynamics.ProjectionTail
import OAI.Probability.LatticeSurface.Dynamics.TwoStageDynamics

namespace OAI

namespace ProjectionComparison

open Set ClusterDisplacement

attribute [local instance] Classical.propDecidable

variable {V E : Type*} [Fintype V] [Fintype E]

noncomputable def meshTail (S : System V E) (b₀ b₁ h₀ h₁ : V → ℝ)
    (hh₀ : h₀∈feasible S b₀) (hh₁ : h₁∈feasible S b₁)
    (increments : ℕ → V → ℝ) (a : ℝ) (n : ℕ) (x : {x // x∉S.pins}) : ℝ :=
  max (recursion S b₁ ⟨h₁,hh₁⟩ h₁ increments n x-
    recursion S b₀ ⟨h₀,hh₀⟩ h₀ increments n x-a) 0

end ProjectionComparison

namespace ProjectionComparison

open Set ClusterDisplacement

attribute [local instance] Classical.propDecidable

variable {V E : Type*} [Fintype V] [Fintype E]

omit [Fintype E] in
lemma recursion_feasible (S : System V E) (b h₀ : V → ℝ) (hh₀ : h₀∈feasible S b)
    (increments : ℕ → V → ℝ) (n : ℕ) : recursion S b ⟨h₀,hh₀⟩ h₀ increments n∈feasible S b := by
  cases n with
  | zero => exact hh₀
  | succ n => exact (project_spec S b ⟨h₀,hh₀⟩ _).1

lemma mesh_tail_step (S : System V E) (b₀ b₁ h₀ h₁ : V → ℝ)
    (hh₀ : h₀∈feasible S b₀) (hh₁ : h₁∈feasible S b₁)
    (increments : ℕ → V → ℝ) (a : ℝ) (hb : ∀x∈S.pins,b₁ x-b₀ x≤a) (n : ℕ) :
    ∃ A B : Kernel {x // x∉S.pins},Firm A ∧ Firm B ∧
      meshTail S b₀ b₁ h₀ h₁ hh₀ hh₁ increments a (n+1)=
        B.apply (A.apply (meshTail S b₀ b₁ h₀ h₁ hh₀ hh₁ increments a n)) := by
  classical
  let f₀ := recursion S b₀ ⟨h₀,hh₀⟩ h₀ increments n
  let f₁ := recursion S b₁ ⟨h₁,hh₁⟩ h₁ increments n
  let v₀ : V → ℝ := fun x => f₀ x+increments n x
  let v₁ : V → ℝ := fun x => f₁ x+increments n x
  let g₀ := recursion S b₀ ⟨h₀,hh₀⟩ h₀ increments (n+1)
  let g₁ := recursion S b₁ ⟨h₁,hh₁⟩ h₁ increments (n+1)
  obtain ⟨A,hA,r,hr,he⟩:=tail_projection_kernel S b₀ b₁ v₀ v₁ g₀ g₁ a
    (project_spec S b₀ ⟨h₀,hh₀⟩ v₀) (project_spec S b₁ ⟨h₁,hh₁⟩ v₁) hb
  let W : Set V := {x | x∉S.pins}
  let u : V → ℝ := fun x => max (v₁ x-v₀ x-a) 0
  have hu (x) : u x=max (f₁ x-f₀ x-a) 0 := by dsimp [u,v₁,v₀];rw [add_sub_add_right_eq_sub]
  have hup (x) (hx : x∉W) : u x=0 := by
    have hp : x∈S.pins := Classical.not_not.mp hx
    rw [hu]
    have hf₀ : f₀ x=b₀ x := (recursion_feasible S b₀ h₀ hh₀ increments n).2 x hp
    have hf₁ : f₁ x=b₁ x := (recursion_feasible S b₁ h₁ hh₁ increments n).2 x hp
    rw [hf₀,hf₁,max_eq_right (sub_nonpos.mpr (hb x hp))]
  refine ⟨A.restrict W,Kernel.cutoff (fun x : W => r x) (fun x => hr x),A.restrict_firm hA W,
    Kernel.cutoff_firm _ _,?_⟩
  funext x
  rw [Kernel.cutoff_apply]
  have harg : meshTail S b₀ b₁ h₀ h₁ hh₀ hh₁ increments a n=(fun x : W => u x) := by
    funext x
    exact (hu x).symm
  rw [harg,Kernel.restrict_apply_of_zero A W u hup]
  exact he x

end ProjectionComparison

namespace ProjectionComparison

open Set ClusterDisplacement

attribute [local instance] Classical.propDecidable

variable {V E : Type*} [Fintype V] [Fintype E]

theorem projection_mesh_tail_displacement (S : System V E) (b₀ b₁ h₀ h₁ : V → ℝ)
    (hh₀ : h₀∈feasible S b₀) (hh₁ : h₁∈feasible S b₁)
    (increments : ℕ → V → ℝ) (a : ℝ) (hb : ∀x∈S.pins,b₁ x-b₀ x≤a)
    (N k : ℕ) (hk : k≤N) (x : {x // x∉S.pins}) :
    |meshTail S b₀ b₁ h₀ h₁ hh₀ hh₁ increments a k x-
      meshTail S b₀ b₁ h₀ h₁ hh₀ hh₁ increments a 0 x|≤
      5*(Fintype.card {x // x∉S.pins}+1:ℝ)*Real.sqrt
        (energy (meshTail S b₀ b₁ h₀ h₁ hh₀ hh₁ increments a 0)-
         energy (meshTail S b₀ b₁ h₀ h₁ hh₀ hh₁ increments a N)) := by
  exact two_stage_displacement _ (mesh_tail_step S b₀ b₁ h₀ h₁ hh₀ hh₁ increments a hb) N k hk x

end ProjectionComparison

end OAI
