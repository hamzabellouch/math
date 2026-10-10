import Mathlib
import OAI.Analysis.BoundedHochschild.CocycleNormalParts
import OAI.Analysis.BoundedHochschild.FactorFinitePaths
import OAI.Analysis.BoundedHochschild.FreeWords
import OAI.Analysis.BoundedHochschild.MatrixDisplacement
import OAI.Analysis.BoundedHochschild.UnitaryLifts

namespace OAI

/-! Countable sets closed under words and prescribed countable witness families. -/

noncomputable section

namespace HochschildLocalization
open BoundedHochschild
variable {M : Type*} [Monoid M] [StarMul M]

def wordSet (S : Set M) : Set M := (Submonoid.closure (S ∪ star S) : Set M)
lemma wordSet_countable {S : Set M} (hS : S.Countable) : (wordSet S).Countable := by
  apply countable_submonoidClosure
  exact hS.union (by simpa only [Set.image_star] using hS.image star)
lemma subset_wordSet (S : Set M) : S ⊆ wordSet S := fun _ h => Submonoid.subset_closure (Or.inl h)
lemma wordSet_mono {S T : Set M} (h : S ⊆ T) : wordSet S ⊆ wordSet T :=
  Submonoid.closure_mono (Set.union_subset_union h (fun _ ha => h ha))

theorem exists_countable_witness_closure
    (D : Set M) (hD : D.Countable) (W : M → ℕ → Set M)
    (hW : ∀ a k, (W a k).Countable) :
    ∃ S : Set M, S.Countable ∧ D ⊆ S ∧ wordSet S ⊆ S ∧
      ∀ a ∈ S, ∀ k, W a k ⊆ S := by
  classical
  let step (S : Set M) := wordSet S ∪ ⋃ a ∈ S, ⋃ k, W a k
  let A : ℕ → Set M := fun n => step^[n] D
  have hsub (n : ℕ) : A n ⊆ A (n+1) := by
    simpa only [A,Function.iterate_succ_apply'] using
      (Set.Subset.trans (subset_wordSet (A n)) (Set.subset_union_left : wordSet (A n) ⊆ step (A n)))
  have hmono : Monotone A := monotone_nat_of_le_succ hsub
  have hcount (n : ℕ) : (A n).Countable := by
    induction n with
    | zero => exact hD
    | succ n ih =>
      rw [show A (n+1)=step (A n) by exact Function.iterate_succ_apply' step n D]
      exact (wordSet_countable ih).union (ih.biUnion (fun a ha => Set.countable_iUnion (hW a)))
  let S := ⋃ n, A n
  have hAS (n : ℕ) : A n ⊆ S := Set.subset_iUnion A n
  have hDS : D ⊆ S := hAS 0
  have hWS : wordSet S ⊆ S := by
    intro x hx
    have hstage : ∃ n, x ∈ wordSet (A n) := by
      induction hx using Submonoid.closure_induction with
      | mem a ha =>
        rcases ha with ha|ha
        · obtain ⟨n,hn⟩ := Set.mem_iUnion.mp ha
          exact ⟨n,Submonoid.subset_closure (Or.inl hn)⟩
        · obtain ⟨n,hn⟩ := Set.mem_iUnion.mp (show star a ∈ S from ha)
          exact ⟨n,Submonoid.subset_closure (Or.inr hn)⟩
      | one => exact ⟨0,Submonoid.one_mem _⟩
      | mul a b _ _ ha hb =>
        obtain ⟨n,hn⟩ := ha
        obtain ⟨m,hm⟩ := hb
        exact ⟨max n m,Submonoid.mul_mem _
          (wordSet_mono (hmono (Nat.le_max_left _ _)) hn)
          (wordSet_mono (hmono (Nat.le_max_right _ _)) hm)⟩
    obtain ⟨n,hn⟩ := hstage
    apply hAS (n+1)
    rw [show A (n+1)=step (A n) by exact Function.iterate_succ_apply' step n D]
    exact Or.inl hn
  refine ⟨S,Set.countable_iUnion hcount,hDS,hWS,?_⟩
  intro a ha k b hb
  obtain ⟨n,hn⟩ := Set.mem_iUnion.mp ha
  apply hAS (n+1)
  rw [show A (n+1)=step (A n) by exact Function.iterate_succ_apply' step n D]
  exact Or.inr (Set.mem_iUnion.mpr ⟨a,Set.mem_iUnion.mpr ⟨hn,Set.mem_iUnion.mpr ⟨k,hb⟩⟩⟩)

end HochschildLocalization

end

end OAI
