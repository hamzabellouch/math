import Mathlib
import OAI.Probability.CriticalPercolation.LinearGroups.FiniteSubspaceOrbit
import OAI.Probability.CriticalPercolation.LinearGroups.LocalFurstenbergBound

namespace OAI

section
noncomputable section
open Set Function Module
open scoped Classical

namespace CriticalPercolation.LinearGrowth
variable {K V G : Type*} [Field K] [AddCommGroup V] [Module K V] [Group G]

def FullSpan (ρ : G →* (V ≃ₗ[K] V)) : Prop :=
  Submodule.span K (Set.range (fun g => (ρ g).toLinearMap))=⊤

def StrongFullSpan (ρ : G →* (V ≃ₗ[K] V)) : Prop :=
  ∀ H : Subgroup G, H.FiniteIndex → FullSpan (ρ.comp H.subtype)

lemma submodule_eq_bot_or_top_of_fullSpan (ρ : G →* (V ≃ₗ[K] V)) (hfull : FullSpan ρ)
    (W : Submodule K V) (hinv : ∀ g, W.map (ρ g).toLinearMap=W) : W=⊥ ∨ W=⊤ := by
  by_cases hW : W=⊥
  · exact Or.inl hW
  right
  obtain ⟨w,hw,hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW
  obtain ⟨φ,hφ⟩ := Projective.exists_dual_eq_one K hw0
  apply top_unique
  intro y _
  let T := φ.smulRight y
  have hT : T∈Submodule.span K (Set.range (fun g => (ρ g).toLinearMap)) := hfull ▸ Submodule.mem_top
  have hm : ∀ A∈Submodule.span K (Set.range (fun g => (ρ g).toLinearMap)), A w∈W := by
    intro A hA
    induction hA using Submodule.span_induction with
    | mem A hA =>
      obtain ⟨g,rfl⟩ := hA
      rw [←hinv g]
      exact Submodule.mem_map.mpr ⟨w,hw,rfl⟩
    | zero => exact W.zero_mem
    | add A B hA hB ihA ihB => exact W.add_mem ihA ihB
    | smul c A hA ihA => exact W.smul_mem c ihA
  simpa only [T,LinearMap.smulRight_apply,hφ,one_smul] using hm T hT

lemma no_finite_subspace_orbit_of_strongFullSpan (ρ : G →* (V ≃ₗ[K] V))
    (hρ : StrongFullSpan ρ) (W : Submodule K V) (hW0 : W≠⊥) (hW1 : W≠⊤) :
    ¬(Set.range (fun g => W.map (ρ g).toLinearMap)).Finite := by
  intro hf
  obtain ⟨H,hHi,hH⟩ := finiteIndex_subspace_stabilizer ρ W hf
  exact (submodule_eq_bot_or_top_of_fullSpan (ρ.comp H.subtype) (hρ H hHi) W hH).elim hW0 hW1

end CriticalPercolation.LinearGrowth
namespace CriticalPercolation.LinearGrowth
variable {K V G : Type*} [NontriviallyNormedField K] [NormedAddCommGroup V]
variable [NormedSpace K V] [ProperSpace K] [FiniteDimensional K V] [Group G]

def continuousRepresentation (ρ : G →* (V ≃ₗ[K] V)) : G →* (V ≃L[K] V) where
  toFun g := (ρ g).toContinuousLinearEquiv
  map_one' := by ext x; change ρ 1 x=x; rw [map_one]; rfl
  map_mul' g h := by ext x; change ρ (g*h) x=ρ g (ρ h x); rw [map_mul]; rfl

lemma projective_bound_of_strongFullSpan [Nontrivial V] [DecidableEq G]
    (ρ : G →* (V ≃ₗ[K] V)) (hρ : StrongFullSpan ρ)
    (S : Finset G) (h1 : (1:G)∈S) (hgen : Subgroup.closure (S:Set G)=⊤)
    (d : ℕ) (hg : SparseGrowth.HasDegree S d) :
    ∃ δ : ℝ, 0<δ ∧ ∀ g : G, ∀ x : V,
      δ*‖(continuousRepresentation ρ g).toContinuousLinearMap‖*‖x‖≤‖ρ g x‖ := by
  rcases LocalProjective.sparse_local_furstenberg_alternative (continuousRepresentation ρ)
    S h1 hgen d hg with horb | hb
  · obtain ⟨W,hW0,hW1,hW⟩ := horb
    exact False.elim (no_finite_subspace_orbit_of_strongFullSpan ρ hρ W hW0 hW1 hW)
  · exact hb

end CriticalPercolation.LinearGrowth
end
end

end OAI
