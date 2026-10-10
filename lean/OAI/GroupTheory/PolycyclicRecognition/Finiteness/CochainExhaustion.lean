import OAI.GroupTheory.PolycyclicRecognition.Analysis.BarChainExhaustion
import OAI.GroupTheory.PolycyclicRecognition.Algebra.ExhaustionFunctionGluing
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality

namespace OAI

/-! # Cochains on an increasing exhaustive sequence of subgroups -/

noncomputable section
namespace PolycyclicRecognition

open CategoryTheory
variable {G : Type} [Group G]

def subgroupCochainRestriction (H : Subgroup G) (A : Rep ℤ G) :
    groupCohomology.inhomogeneousCochains A ⟶
      groupCohomology.inhomogeneousCochains (Rep.res H.subtype A) :=
  groupCohomology.cochainsMap H.subtype (𝟙 (Rep.res H.subtype A))

theorem subgroupCochainRestriction_apply (H : Subgroup G) (A : Rep ℤ G) (k : ℕ)
    (f : (Fin k → G) → A) (a : Fin k → H) :
    (subgroupCochainRestriction H A).f k f a = f (fun i => a i) := rfl

theorem cochains_eq_of_exhaustive_restrictions (S : ℕ → Subgroup G)
    (hS : Monotone S) (hcover : ∀ g, ∃ n, g ∈ S n) (A : Rep ℤ G) (k : ℕ)
    {f g : (Fin k → G) → A}
    (h : ∀ n, (subgroupCochainRestriction (S n) A).f k f =
      (subgroupCochainRestriction (S n) A).f k g) : f = g := by
  classical
  funext a
  obtain ⟨n, hn⟩ := finite_subset_subgroup_exhaustion S hS hcover (Finset.univ.image a)
  let b : Fin k → S n := fun i => ⟨a i, hn (a i) (Finset.mem_image.mpr ⟨i, by simp, rfl⟩)⟩
  exact congrFun (h n) b

theorem exists_cochain_of_compatible_restrictions (S : ℕ → Subgroup G)
    (hS : Monotone S) (hcover : ∀ g, ∃ n, g ∈ S n) (A : Rep ℤ G) (k : ℕ)
    (f : ∀ n, (Fin k → S n) → A)
    (hf : ∀ n (a : Fin k → S n),
      f (n + 1) (fun i => ⟨a i, hS (Nat.le_succ n) (a i).property⟩) = f n a) :
    ∃ g : (Fin k → G) → A, ∀ n,
      (subgroupCochainRestriction (S n) A).f k g = f n := by
  classical
  let T (n : ℕ) : Set (Fin k → G) := {a | ∀ i, a i ∈ S n}
  have hT : Monotone T := fun n m hnm a ha i => hS hnm (ha i)
  have hcoverT (a : Fin k → G) : ∃ n, a ∈ T n := by
    obtain ⟨n, hn⟩ := finite_subset_subgroup_exhaustion S hS hcover (Finset.univ.image a)
    exact ⟨n, fun i => hn (a i) (Finset.mem_image.mpr ⟨i, by simp, rfl⟩)⟩
  let F (n : ℕ) (a : T n) := f n (fun i => ⟨a.val i, a.property i⟩)
  have hF (n : ℕ) (a : T n) :
      F (n + 1) ⟨a, hT (Nat.le_succ n) a.property⟩ = F n a :=
    hf n (fun i => ⟨a.val i, a.property i⟩)
  obtain ⟨g, hg⟩ := exists_function_of_compatible_exhaustion T hT hcoverT F hF
  refine ⟨g, ?_⟩
  intro n
  funext a
  exact hg n ⟨fun i => a i, fun i => (a i).property⟩

end PolycyclicRecognition

end

end OAI
