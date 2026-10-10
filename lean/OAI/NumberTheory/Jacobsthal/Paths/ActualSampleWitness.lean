import OAI.NumberTheory.Jacobsthal.Partitions.GoodSampleSelection

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace ErdosInverseCounts
open NumberTheoryLean

def NodeBadEdge (Y : ℕ) (small : Finset ℕ) (a : ℕ → ℕ) (delta V0 : ℝ) (m u : ℕ) : Prop :=
  |(modulusCount Y small a (m*u) : ℝ)-(modulusCount Y small a m : ℝ)/(u : ℝ)| >
    delta*(Y : ℝ)*V0/((m : ℝ)*(u : ℝ))

def WitnessingBadEdge (Y : ℕ) (small : Finset ℕ) (a : ℕ → ℕ) (delta V0 : ℝ) (p q u : ℕ) : Prop :=
  NodeBadEdge Y small a delta V0 (p*q) u

theorem modulusCount_child_mass (Y : ℕ) (small : Finset ℕ) (a : ℕ → ℕ)
    (m u : ℕ) (P : Finset ℕ) (hm : m ≠ 0) (hu : Nat.Prime u) :
    modulusCount Y small a (m*u) = ResidueSieveTree.mass Y small a
      (ResidueSieveTree.child (m.primeFactors,P) u) := by
  unfold modulusCount modulusCandidates ResidueSieveTree.mass ResidueSieveTree.child
  rw [Nat.primeFactors_mul hm hu.ne_zero,hu.primeFactors,Finset.union_singleton]

theorem nodeBadEdge_iff_tree_mass (Y : ℕ) (small : Finset ℕ) (a : ℕ → ℕ)
    (delta V0 : ℝ) (m u : ℕ) (P : Finset ℕ) (hm : m ≠ 0) (hu : Nat.Prime u) :
    NodeBadEdge Y small a delta V0 m u ↔
      |(ResidueSieveTree.mass Y small a (ResidueSieveTree.child (m.primeFactors,P) u) : ℝ)-
        (ResidueSieveTree.mass Y small a (m.primeFactors,P) : ℝ)/(u : ℝ)| >
          delta*(Y : ℝ)*V0/((m : ℝ)*(u : ℝ)) := by
  rw [NodeBadEdge,modulusCount_child_mass Y small a m u P hm hu,modulusCount_eq_mass Y small a m P]

theorem literal_witnessing_bad_edge (Y : ℕ) (small : Finset ℕ) (a : ℕ → ℕ)
    (delta V0 : ℝ) (p q u : ℕ) :
    WitnessingBadEdge Y small a delta V0 p q u ↔
      |((NumberTheoryLean.SievePartition.residueCandidates Y (p*q*u).primeFactors small a).card : ℝ)-
        ((NumberTheoryLean.SievePartition.residueCandidates Y (p*q).primeFactors small a).card : ℝ)/(u : ℝ)| >
          delta*(Y : ℝ)*V0/((p : ℝ)*(q : ℝ)*(u : ℝ)) := by
  simp only [WitnessingBadEdge,NodeBadEdge,modulusCount,modulusCandidates,Int.cast_natCast,Nat.cast_mul]

end ErdosInverseCounts

end

section

namespace ErdosInverseSampleCost
open NumberTheoryLean ErdosInverseStructured ErdosInverseCounts ErdosInverseSampling

def actualWitness (Y : ℕ) (small : Finset ℕ) (a : ℕ → ℕ) (delta V0 : ℝ)
    (P : Finset ℕ) (S R Z cp : ℝ) (pair : ℕ × ℕ) (u : ℕ) : Prop :=
  Nonstructured P (fun p => (a p : ℤ)) S R Z cp pair.1 pair.2 ∧
    WitnessingBadEdge Y small a delta V0 pair.1 pair.2 u

theorem selected_actual_witness (Y : ℕ) (small : Finset ℕ) (a : ℕ → ℕ) (delta V0 : ℝ)
    (P C U : Finset ℕ) (S R Z cp : ℝ) (h : ℕ) (s : Sample U h) (pair : ℕ × ℕ) :
    pair ∈ selectedPairs (P.product C) U (actualWitness Y small a delta V0 P S R Z cp) h s ↔
      pair.1 ∈ P ∧ pair.2 ∈ C ∧ ∀ i : Fin h,
        Nonstructured P (fun p => (a p : ℤ)) S R Z cp pair.1 pair.2 ∧
          WitnessingBadEdge Y small a delta V0 pair.1 pair.2 (s i).val := by
  classical
  rcases pair with ⟨p,q⟩
  constructor
  · intro hmem
    obtain ⟨hpq,htests⟩ := Finset.mem_filter.mp hmem
    obtain ⟨hp,hq⟩ := Finset.mem_product.mp hpq
    exact ⟨hp,hq,htests⟩
  · rintro ⟨hp,hq,htests⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hp,hq⟩,htests⟩

theorem actualWitness_iff_counts (Y : ℕ) (small : Finset ℕ) (a : ℕ → ℕ) (delta V0 : ℝ)
    (P : Finset ℕ) (S R Z cp : ℝ) (p q u : ℕ) :
    actualWitness Y small a delta V0 P S R Z cp (p,q) u ↔
      Nonstructured P (fun p => (a p : ℤ)) S R Z cp p q ∧
        |((SievePartition.residueCandidates Y (p*q*u).primeFactors small a).card : ℝ)-
          ((SievePartition.residueCandidates Y (p*q).primeFactors small a).card : ℝ)/(u : ℝ)| >
            delta*(Y : ℝ)*V0/((p : ℝ)*(q : ℝ)*(u : ℝ)) := by
  rw [actualWitness,literal_witnessing_bad_edge]

theorem selected_actual_witness_positive (Y : ℕ) (small : Finset ℕ) (a : ℕ → ℕ) (delta V0 : ℝ)
    (P C U : Finset ℕ) (S R Z cp : ℝ) (h : ℕ) (hh : 0 < h) (s : Sample U h) (pair : ℕ × ℕ) :
    pair ∈ selectedPairs (P.product C) U (actualWitness Y small a delta V0 P S R Z cp) h s ↔
      pair.1 ∈ P ∧ pair.2 ∈ C ∧ Nonstructured P (fun p => (a p : ℤ)) S R Z cp pair.1 pair.2 ∧
        ∀ i : Fin h,WitnessingBadEdge Y small a delta V0 pair.1 pair.2 (s i).val := by
  rw [selected_actual_witness]
  constructor
  · rintro ⟨hp,hq,htests⟩
    exact ⟨hp,hq,(htests ⟨0,hh⟩).1,fun i => (htests i).2⟩
  · rintro ⟨hp,hq,hnon,htests⟩
    exact ⟨hp,hq,fun i => ⟨hnon,htests i⟩⟩

end ErdosInverseSampleCost

end

end Erdos970

end OAI
