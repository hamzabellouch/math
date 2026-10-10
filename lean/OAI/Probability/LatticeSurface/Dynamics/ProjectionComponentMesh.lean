import Mathlib
import OAI.Probability.LatticeSurface.Dynamics.ProjectionRestrictionMesh

namespace OAI

namespace ProjectionComparison

open Set Filter ClusterDisplacement

attribute [local instance] Classical.propDecidable

variable {V E : Type*} [Fintype V] [Fintype E]

noncomputable def componentMeshTail (S : System V E) (W : Set V)
    (b₀ b₁ h₀ h₁ : V → ℝ) (hh₀ : h₀∈feasible S b₀) (hh₁ : h₁∈feasible S b₁)
    (inc : ℕ → V → ℝ) (a : ℝ) (n : ℕ) : {x : W // x.val∉S.pins} → ℝ :=
  fun x => meshTail S b₀ b₁ h₀ h₁ hh₀ hh₁ inc a n ⟨x.val.val,x.property⟩

def componentPathTail (S : System V E) (W : Set V) (u₀ u₁ : ℝ → V → ℝ) (a t : ℝ) :
    {x : W // x.val∉S.pins} → ℝ := fun x => max (u₁ t x.val.val-u₀ t x.val.val-a) 0

end ProjectionComparison

namespace ProjectionComparison

open Set Filter ClusterDisplacement

attribute [local instance] Classical.propDecidable

variable {V E : Type*} [Fintype V] [Fintype E]

lemma component_mesh_displacement (S : System V E) (W : Set V) (hW : S.pins⊆W)
    (b₀ b₁ h₀ h₁ : V → ℝ) (hh₀ : h₀∈feasible S b₀) (hh₁ : h₁∈feasible S b₁)
    (inc : ℕ → V → ℝ) (a : ℝ) (hb : ∀x∈S.pins,b₁ x-b₀ x≤a) (N : ℕ)
    (hcut₀ : ∀i<N,∀e,
      recursion S b₀ ⟨h₀,hh₀⟩ h₀ inc (i+1) (S.left e)-recursion S b₀ ⟨h₀,hh₀⟩ h₀ inc (i+1) (S.right e)=S.cost e →
      S.left e∉S.pins → S.right e∉S.pins → (S.left e∈W ↔ S.right e∈W))
    (hcut₁ : ∀i<N,∀e,
      recursion S b₁ ⟨h₁,hh₁⟩ h₁ inc (i+1) (S.left e)-recursion S b₁ ⟨h₁,hh₁⟩ h₁ inc (i+1) (S.right e)=S.cost e →
      S.left e∉S.pins → S.right e∉S.pins → (S.left e∈W ↔ S.right e∈W))
    (k : ℕ) (hk : k≤N) (x : {x : W // x.val∉S.pins}) :
    |componentMeshTail S W b₀ b₁ h₀ h₁ hh₀ hh₁ inc a k x-
      componentMeshTail S W b₀ b₁ h₀ h₁ hh₀ hh₁ inc a 0 x| ≤
      5*(Fintype.card {x : W // x.val∉S.pins}+1:ℝ)*
        Real.sqrt (energy (componentMeshTail S W b₀ b₁ h₀ h₁ hh₀ hh₁ inc a 0)-
          energy (componentMeshTail S W b₀ b₁ h₀ h₁ hh₀ hh₁ inc a N)) := by
  have hr₀ := recursion_restrict S W hW b₀ h₀ hh₀ inc N hcut₀
  have hr₁ := recursion_restrict S W hW b₁ h₁ hh₁ inc N hcut₁
  have he (i : ℕ) (hi : i≤N) :
      meshTail (restrictedSystem S W) (fun x => b₀ x) (fun x => b₁ x)
        (fun x => h₀ x) (fun x => h₁ x) (feasible_restrict S W b₀ h₀ hh₀)
        (feasible_restrict S W b₁ h₁ hh₁) (fun i x => inc i x) a i=
      componentMeshTail S W b₀ b₁ h₀ h₁ hh₀ hh₁ inc a i := by
    funext x
    change max (_-_-a) 0=max (_-_-a) 0
    rw [←congrFun (hr₀ i hi) x.val,←congrFun (hr₁ i hi) x.val]
  have ht := projection_mesh_tail_displacement (restrictedSystem S W) (fun x => b₀ x) (fun x => b₁ x)
    (fun x => h₀ x) (fun x => h₁ x) (feasible_restrict S W b₀ h₀ hh₀)
    (feasible_restrict S W b₁ h₁ hh₁) (fun i x => inc i x) a (fun x hx => hb x hx) N k hk x
  rw [he k hk,he 0 (Nat.zero_le N),he N le_rfl] at ht
  exact ht

end ProjectionComparison

end OAI
