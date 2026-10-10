import Mathlib
import OAI.Probability.LatticeSurface.Dynamics.ProjectionComponentMesh

namespace OAI

namespace ProjectionComparison

open Set Filter ClusterDisplacement

attribute [local instance] Classical.propDecidable

variable {V E : Type*} [Fintype V] [Fintype E]

lemma mesh_tail_energy_antitone (S : System V E) (b₀ b₁ h₀ h₁ : V → ℝ)
    (hh₀ : h₀∈feasible S b₀) (hh₁ : h₁∈feasible S b₁)
    (inc : ℕ → V → ℝ) (a : ℝ) (hb : ∀x∈S.pins,b₁ x-b₀ x≤a) :
    Antitone (fun i => energy (meshTail S b₀ b₁ h₀ h₁ hh₀ hh₁ inc a i)) := by
  apply antitone_nat_of_succ_le
  intro i
  obtain ⟨A,B,hA,hB,he⟩ := mesh_tail_step S b₀ b₁ h₀ h₁ hh₀ hh₁ inc a hb i
  rw [he]
  exact (B.energy_bound _).trans (A.energy_bound _)

lemma component_mesh_loss_nonneg (S : System V E) (W : Set V) (hW : S.pins⊆W)
    (b₀ b₁ h₀ h₁ : V → ℝ) (hh₀ : h₀∈feasible S b₀) (hh₁ : h₁∈feasible S b₁)
    (inc : ℕ → V → ℝ) (a : ℝ) (hb : ∀x∈S.pins,b₁ x-b₀ x≤a) (N : ℕ)
    (hcut₀ : ∀i<N,∀e,
      recursion S b₀ ⟨h₀,hh₀⟩ h₀ inc (i+1) (S.left e)-recursion S b₀ ⟨h₀,hh₀⟩ h₀ inc (i+1) (S.right e)=S.cost e →
      S.left e∉S.pins → S.right e∉S.pins → (S.left e∈W ↔ S.right e∈W))
    (hcut₁ : ∀i<N,∀e,
      recursion S b₁ ⟨h₁,hh₁⟩ h₁ inc (i+1) (S.left e)-recursion S b₁ ⟨h₁,hh₁⟩ h₁ inc (i+1) (S.right e)=S.cost e →
      S.left e∉S.pins → S.right e∉S.pins → (S.left e∈W ↔ S.right e∈W))
    : 0≤energy (componentMeshTail S W b₀ b₁ h₀ h₁ hh₀ hh₁ inc a 0)-
      energy (componentMeshTail S W b₀ b₁ h₀ h₁ hh₀ hh₁ inc a N) := by
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
  have ht := mesh_tail_energy_antitone (restrictedSystem S W) (fun x => b₀ x) (fun x => b₁ x)
    (fun x => h₀ x) (fun x => h₁ x) (feasible_restrict S W b₀ h₀ hh₀)
    (feasible_restrict S W b₁ h₁ hh₁) (fun i x => inc i x) a (fun x hx => hb x hx) (Nat.zero_le N)
  dsimp only at ht
  rw [he 0 (Nat.zero_le N),he N le_rfl] at ht
  exact sub_nonneg.mpr ht

end ProjectionComparison

end OAI
