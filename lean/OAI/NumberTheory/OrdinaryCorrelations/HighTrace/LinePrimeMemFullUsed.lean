import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.IntegerResidues
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.PrivateFamily
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.AmplitudeGeOne
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.Restrict
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.FactorsAppendSubset
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.Ordered

namespace OAI

noncomputable section
open scoped BigOperators
open Finset
open Finset Classical
open Filter
open Finset Classical Filter
open scoped Topology

namespace OrdinaryCorrelations.GraphKernel.PrimeSystem
open OrdinaryCorrelations.ArithmeticSaving OrdinaryCorrelations.SignedTrace
open Finset Classical
variable {S : PrimeSystem} {B τ C₀ : ℝ} {D : S.DivisorFamily B τ C₀} {h L ℓ n : ℕ}

lemma line_prime_mem_fullUsed (w : ClosedLine h ℓ) (𝔏 : List (AttachedSpec w D L))
    (p : S.Index) {i : Fin ℓ} (hi : (p:ℕ) ∈ (w.label i).primeFactors) :
    p ∈ fullUsedIndices w 𝔏 :=
  mem_filter.mpr ⟨mem_univ _,Or.inl ⟨i,(Nat.mem_primeFactors.mp hi).2.1⟩⟩

lemma list_prime_mem_fullUsed (w : ClosedLine h ℓ) (𝔏 : List (AttachedSpec w D L))
    (s : AttachedSpec w D L) (hs : s ∈ 𝔏) (p : S.Index) (hp : (p:ℕ) ∈ s.spec.primeSupport) :
    p ∈ fullUsedIndices w 𝔏 := by
  apply mem_filter.mpr
  exact ⟨mem_univ _,Or.inr (mem_biUnion.mpr ⟨s,List.mem_toFinset.mpr hs,hp⟩)⟩

lemma LineExpression.factors_fullUsed (w : ClosedLine h ℓ) (hl : ∀ i, w.label i ∈ D.members)
    (𝔏 : List (AttachedSpec w D L)) (a b : Fin (ℓ+1)) (i : Fin ℓ) :
    (segment w hl a b).factors i ⊆ fullUsedIndices w 𝔏 := by
  intro p hp
  exact line_prime_mem_fullUsed w 𝔏 p ((mem_labelPrimeSet (w.label i) (hl i) p).mp hp)

lemma Specification.factors_fullUsed (w : ClosedLine h ℓ) (𝔏 : List (AttachedSpec w D L))
    (s : AttachedSpec w D L) (hs : s ∈ 𝔏) (a b : ℕ) (i : Fin L) :
    (s.spec.segmentExpression a b).factors i ⊆ fullUsedIndices w 𝔏 := by
  intro p hp
  change p ∈ (if hi : i.val < s.spec.length then
    labelPrimeSet (s.spec.label ⟨i.val,hi⟩) (s.spec.label_mem _) else ∅) at hp
  split_ifs at hp with hi
  · apply list_prime_mem_fullUsed w 𝔏 s hs p
    exact mem_insert_of_mem (mem_biUnion.mpr
      ⟨⟨i.val,hi⟩,mem_univ _,(mem_labelPrimeSet _ _ _).mp hp⟩)
  · simp at hp

namespace PrivateFamily
variable {w : ClosedLine h ℓ} (F : PrivateFamily w D L n)

noncomputable def used (l : List (AttachedSpec w D L)) : Finset S.Index :=
  fullUsedIndices w (l++List.ofFn F.witness)

lemma witness_prime_mem_used (l : List (AttachedSpec w D L)) (j : Fin n)
    (p : S.Index) (hp : (p:ℕ) ∈ (F.witness j).spec.primeSupport) : p ∈ F.used l :=
  list_prime_mem_fullUsed w _ (F.witness j)
    (List.mem_append_right _ (List.mem_ofFn.mpr ⟨j,rfl⟩)) p hp

lemma test_support_used {j : Fin n} (l : List (AttachedSpec w D L))
    (t : F.Test j) (p : S.Index) (hp : (p:ℕ) ∈ t.support) : p ∈ F.used l := by
  cases t with
  | extra | tail => exact F.witness_prime_mem_used l j p hp
  | compare i q r hi =>
    rcases mem_union.mp hp with hp|hp
    · rcases mem_union.mp hp with hp|hp
      · exact F.witness_prime_mem_used l i p hp
      · exact F.witness_prime_mem_used l j p hp
    · obtain ⟨i,hi,hp⟩ := mem_biUnion.mp hp
      exact line_prime_mem_fullUsed w _ p hp

lemma test_factors_used (hl : ∀ i, w.label i ∈ D.members)
    (l : List (AttachedSpec w D L)) {j : Fin n} (t : F.Test j) :
    ∀ i, (t.symbolic hl).factors i ⊆ F.used l := by
  have hs (j : Fin n) (a b : ℕ) :
      ∀ i, ((F.witness j).spec.segmentExpression a b).factors i ⊆ F.used l :=
    Specification.factors_fullUsed w _ (F.witness j)
      (List.mem_append_right _ (List.mem_ofFn.mpr ⟨j,rfl⟩)) a b
  have hz (E : ℕ) : ∀ i, (SquarefreeExpression.zeroExpression S.Index E).factors i ⊆ F.used l :=
    fun _ => empty_subset _
  cases t with
  | extra | tail =>
    apply SquarefreeExpression.factors_append_subset
    · exact SquarefreeExpression.factors_append_subset _ _ _ (hz _) (hs _ _ _)
    · exact hz _
  | compare i q r hi =>
    apply SquarefreeExpression.factors_append_subset
    · apply SquarefreeExpression.factors_append_subset
      · exact LineExpression.factors_fullUsed w hl _ _ _
      · exact hs _ _ _
    · exact hs i 0 ((F.witness i).spec.activity r hi).val

lemma used_card_le (l : List (AttachedSpec w D L)) (hl : ∀ i, w.label i ∈ D.members) :
    (F.used l).card ≤ ℓ*⌈C₀*Real.log B⌉₊+(l.length+n)*(L*⌈C₀*Real.log B⌉₊+1) := by
  simpa only [used,List.length_append,List.length_ofFn] using fullUsedIndices_card_le w (l++List.ofFn F.witness) hl

noncomputable def usedEmbedding (l : List (AttachedSpec w D L))
    (c : Case) (A : Finset (Fin n)) (t : ∀ j : A, F.Test j.val)
    (ht : ∀ j, (t j).Valid) (hinj : Function.Injective (fun j => (t j).selected)) :
    Fin A.card ↪ F.used l :=
  TriangularExpressions.restrictEmbedding (F.used l)
    (fun i => F.test_support_used l _ _ ((t (c.ordered A i)).selected_mem (ht _)))
    (e:=testEmbedding c A t hinj)

noncomputable def usedTestSystem (hl : ∀ i, w.label i ∈ D.members)
    (l : List (AttachedSpec w D L)) (c : Case) (A : Finset (Fin n)) (t : ∀ j : A, F.Test j.val)
    (ht : ∀ j, (t j).Valid) (hinj : Function.Injective (fun j => (t j).selected))
    (hfuture : ∀ i j : A, c.Precedes i.val j.val → ((t j).selected:ℕ) ∉ (t i).support) :
    TriangularExpressions (F.usedEmbedding l c A t ht hinj) ((ℓ+L)+L) :=
  (testSystem hl c A t ht hinj hfuture).restrict (F.used l)
    (fun i => F.test_support_used l _ _ ((t (c.ordered A i)).selected_mem (ht _)))
    (fun i => F.test_support_used l _ _ ((t (c.ordered A i)).modulus_mem))

lemma usedTestSystem_admissible (hl : ∀ i, w.label i ∈ D.members)
    (l : List (AttachedSpec w D L)) (c : Case) (A : Finset (Fin n)) (t : ∀ j : A, F.Test j.val)
    (ht : ∀ j, (t j).Valid) (hinj : Function.Injective (fun j => (t j).selected))
    (hfuture : ∀ i j : A, c.Precedes i.val j.val → ((t j).selected:ℕ) ∉ (t i).support)
    (hnd : ∀ j, if (t j).Linear then ¬(((t j).modulus:ℕ):ℤ) ∣ (t j).coefficient
      else (t j).expression ≠ 0)
    (hB : 0 ≤ B) (P : ℝ) (hP : ∀ p : S.Index, P ≤ (p:ℝ))
    (hupper : ∀ p : S.Index, (p:ℝ) ≤ Real.exp B)
    (r : S.Residues) (hq : ∀ i p, (F.witness i).spec.ResidueTest p (F.witness i).vertex (r p)) :
    (F.usedTestSystem hl l c A t ht hinj hfuture).Admissible P (testSize B C₀ h ℓ L)
      (fun p => (p.val:ℕ)) := by
  apply TriangularExpressions.admissible_restrict
  · intro i j
    exact F.test_factors_used hl l (t (c.ordered A i)) j
  · exact testSystem_admissible hl c A t ht hinj hfuture hnd hB P hP hupper r hq

end PrivateFamily
end OrdinaryCorrelations.GraphKernel.PrimeSystem

end

end OAI
