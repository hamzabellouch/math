import Mathlib
import OAI.Combinatorics.TriangleRemoval.Process.SparseScalingOne
import OAI.Combinatorics.TriangleRemoval.Embeddings.RestrictLabel

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open scoped BigOperators ENNReal Classical
open Filter MeasureTheory
open Filter
open scoped BigOperators Topology
open scoped BigOperators

namespace SharpTerminalLeave

noncomputable def emptyRootInjection {k n : ℕ} (T : RootedTemplate k) (hT : T.roots = ∅) :
    {x // x ∈ T.roots} ↪ Fin n where
  toFun x := False.elim (by simpa [hT] using x.property)
  inj' := by intro x; exact False.elim (by simpa [hT] using x.property)

theorem rootedCount_empty_roots {k n : ℕ} (T : RootedTemplate k) (hT : T.roots = ∅)
    (ψ : {x // x ∈ T.roots} ↪ Fin n) (G : Graph n) :
    rootedCount T ψ G = ((graphEmbeddingSet T.edges G).card : ℝ) := by
  classical
  let e : RootedInjection T ψ ≃ (Fin k ↪ Fin n) :=
    { toFun := Subtype.val
      invFun := fun φ => ⟨φ,fun x => False.elim (by simpa [hT] using x.property)⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  unfold rootedCount copyCount
  calc
    _ = ∑ φ : Fin k ↪ Fin n, intact (T.edges.image (fun e => e.map φ)) G :=
      Fintype.sum_equiv e _ _ (fun _ => rfl)
    _ = _ := by simp [graphEmbeddingSet,intact]

def unrootedTemplate {N : ℕ} (E : Graph N) (hE : ∀ e ∈ E, e.card = 2) : RootedTemplate N where
  edges := E
  roots := ∅
  simple := hE
  independent := by
    intro e he hemp
    have hz : e = ∅ := Finset.subset_empty.mp hemp
    have hh := hE e he
    rw [hz,Finset.card_empty] at hh
    omega

theorem graphEmbeddingSet_large_count {n N : ℕ} {G : Graph n} {c C : ℝ}
    (hGood : GoodPrefixGraph n c C G) (E : Graph N) (hE : ∀ e ∈ E, e.card = 2)
    (hcap : N ≤ prefixTemplateCap)
    (hsparse : ∀ U : Finset (Fin N), (E.filter (· ⊆ U)).card ≤ 2 * U.card)
    (hp : 0 ≤ prefixDensity n) (hp1 : prefixDensity n ≤ 1) (hD : 1 ≤ prefixD n) :
    ((graphEmbeddingSet E G).card : ℝ) ≤
      prefixTemplateFactor n C * ((n : ℝ)^N * prefixDensity n ^ E.card) := by
  let T := unrootedTemplate E hE
  let ψ := emptyRootInjection (n := n) T rfl
  have h := (hGood.2.2.2.2.2 N hcap T ψ).1
    (largeTemplateEligible_of_sparse T rfl (prefixDensity n) hp hp1 hD hsparse)
  rw [rootedCount_empty_roots T rfl ψ G] at h
  simpa only [T,unrootedTemplate,rootedScaling,Finset.card_empty,Nat.sub_zero] using h

end SharpTerminalLeave

end

end OAI
