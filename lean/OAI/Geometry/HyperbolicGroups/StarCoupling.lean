import Mathlib
import OAI.Geometry.HyperbolicGroups.ConditionalStar
import OAI.Geometry.HyperbolicGroups.LeafFiber
import OAI.Geometry.HyperbolicGroups.FiberLaw

namespace OAI

section
section


noncomputable section
open scoped BigOperators
namespace HyperbolicObstruction
namespace StarModel
variable {F R A : Type*} [Fintype F] [Fintype R] [Fintype A]
  [DecidableEq F] [DecidableEq A] {k : ℕ}

/-- Forgetting the auxiliary injectivity retains an actual conditional star of
master matches. Its common tuple is named by I. -/
def toConditional (support : R → Finset F) (U I : Finset F) (hI : I ⊆ U)
    (w : TableModel.Entry (A := A) support → Bool) (z : Stars (B := Fin (k+1)) support U w) :
    ConditionalStar (fun a : Matches support w => a.val) I k :=
  ⟨fun j => starBranch support U w j z,by
    intro j f hf
    have hu := hI hf
    simp [starBranch,coord,hu]⟩

def coupling (support : R → Finset F) (U I : Finset F) (hI : I ⊆ U)
    (w : TableModel.Entry (A := A) support → Bool)
    [Nonempty (Stars (B := Fin (k+1)) support U w)] :
    FiniteLaw (ConditionalStar (fun a : Matches support w => a.val) I k) :=
  (FiniteLaw.uniform : FiniteLaw (Stars (B := Fin (k+1)) support U w)).map (toConditional support U I hI w)

lemma coupling_branch (support : R → Finset F) (U I : Finset F) (hI : I ⊆ U)
    (w : TableModel.Entry (A := A) support → Bool)
    [Nonempty (Stars (B := Fin (k+1)) support U w)] (j : Fin (k+1)) :
    (coupling support U I hI w).map (ConditionalStar.branch j) =
      (FiniteLaw.uniform : FiniteLaw (Stars (B := Fin (k+1)) support U w)).map (starBranch support U w j) := by
  rw [coupling,FiniteLaw.map_map]
  rfl

lemma coupling_branch_bound (support : R → Finset F) (U I : Finset F) (hI : I ⊆ U)
    (w : TableModel.Entry (A := A) support → Bool)
    [Nonempty (Stars (B := Fin (k+1)) support U w)] [Nonempty (Matches support w)]
    (j : Fin (k+1)) (a : ℝ) :
    ((coupling support U I hI w).map (ConditionalStar.branch j)).totalVariation FiniteLaw.uniform ≤
      (∑ σ : Matches support w, |(extensionCount support U j (branchValues U σ.val) w : ℝ) - a|) /
        Fintype.card (Stars (B := Fin (k+1)) support U w) := by
  rw [coupling_branch]
  simpa only [card_branch_fiber] using FiniteLaw.uniform_map_bound (starBranch support U w j) a

lemma coupling_leaves (support : R → Finset F) (U I : Finset F) (hI : I ⊆ U)
    (e : F) (he : e ∉ U) (w : TableModel.Entry (A := A) support → Bool)
    [Nonempty (Stars (B := Fin (k+1)) support U w)] :
    (coupling support U I hI w).map (fun z j => (ConditionalStar.branch j z).val e) =
      ((FiniteLaw.uniform : FiniteLaw (Stars (B := Fin (k+1)) support U w)).map
        (starLeaves support U e he w)).map (fun b : Fin (k+1) ↪ A => (b : Fin (k+1) → A)) := by
  rw [coupling,FiniteLaw.map_map,FiniteLaw.map_map]
  rfl

lemma leaf_distribution_bound (support : R → Finset F) (U : Finset F)
    (e : F) (he : e ∉ U) (w : TableModel.Entry (A := A) support → Bool)
    [Nonempty (Stars (B := Fin (k+1)) support U w)] [Nonempty (Fin (k+1) ↪ A)]
    (a₀ : A) (b : ℝ) :
    ((FiniteLaw.uniform : FiniteLaw (Stars (B := Fin (k+1)) support U w)).map
      (starLeaves support U e he w)).totalVariation FiniteLaw.uniform ≤
      (∑ a : Fin (k+1) ↪ A, |(leafCount support U e (leafValues U a a₀) w : ℝ) - b|) /
        Fintype.card (Stars (B := Fin (k+1)) support U w) := by
  have hh := FiniteLaw.uniform_map_bound (starLeaves (B := Fin (k+1)) support U e he w) b
  have hc (a : Fin (k+1) ↪ A) :
      Fintype.card {z : Stars (B := Fin (k+1)) support U w // starLeaves support U e he w z = a} =
        leafCount support U e (leafValues U a a₀) w :=
    card_leaf_fiber support U e he w a a₀
  simp_rw [hc] at hh
  exact hh

/-- Both quantitative conclusions of the deterministic normalization lemma.
The last term is solely the distinct-versus-iid error; no conditional
independence from the common tuple has been assumed. -/
lemma coupling_leaves_bound (support : R → Finset F) (U I : Finset F) (hI : I ⊆ U)
    (e : F) (he : e ∉ U) (w : TableModel.Entry (A := A) support → Bool)
    [Nonempty (Stars (B := Fin (k+1)) support U w)] [Nonempty (Fin (k+1) ↪ A)] [Nonempty A]
    (a₀ : A) (b : ℝ) :
    ((coupling support U I hI w).map (fun z j => (ConditionalStar.branch j z).val e)).totalVariation
      (FiniteLaw.uniform : FiniteLaw (Fin (k+1) → A)) ≤
      (∑ a : Fin (k+1) ↪ A, |(leafCount support U e (leafValues U a a₀) w : ℝ) - b|) /
        Fintype.card (Stars (B := Fin (k+1)) support U w) +
      ((FiniteLaw.uniform : FiniteLaw (Fin (k+1) ↪ A)).map
        (fun a : Fin (k+1) ↪ A => (a : Fin (k+1) → A))).totalVariation
        (FiniteLaw.uniform : FiniteLaw (Fin (k+1) → A)) := by
  rw [coupling_leaves support U I hI e he w]
  apply (FiniteLaw.totalVariation_triangle _
    ((FiniteLaw.uniform : FiniteLaw (Fin (k+1) ↪ A)).map (fun a : Fin (k+1) ↪ A => (a : Fin (k+1) → A))) _).trans
  apply add_le_add _ le_rfl
  apply (FiniteLaw.totalVariation_map_le _ _ (fun a : Fin (k+1) ↪ A => (a : Fin (k+1) → A))).trans
  exact leaf_distribution_bound support U e he w a₀ b

end StarModel
end HyperbolicObstruction
end
end

section

end
end

end OAI
