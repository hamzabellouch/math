import OAI.NumberTheory.Jacobsthal.Paths.FullBoxPrefixLower

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970


namespace NumberTheoryLean.SourcePrimeProductData
open FinitePathGeometry PrimeHistories ReferenceAdmission LogarithmicBinPartition
open ErdosPrimeInputs.PrimePrefixMass

theorem source_word_product_data {w top : ℝ} (hw : 1 < w) (htop : w < top) (ps : List ℕ)
    (hd : ps.Pairwise (· > ·)) (hp : ∀ p∈ps,p ∈ sourcePrimeSet w top) :
    0 < ps.prod ∧ Squarefree ps.prod ∧ ∀ p∈ps.prod.primeFactors,w<(p:ℝ) := by
  have hn : ps.Nodup := hd.imp (fun h => ne_of_gt h)
  have hprime : ∀ p∈ps,p.Prime := fun p h => ((mem_sourcePrimeSet (zero_lt_one.trans hw) htop p).mp (hp p h)).1
  have hpos : 0 < ps.prod := List.prod_pos (fun p h => (hprime p h).pos)
  have he : (∏ p∈ps.toFinset,p)=ps.prod := by simpa using List.prod_toFinset (fun p : ℕ => p) hn
  have hprimeF : ∀ p∈ps.toFinset,p.Prime := fun p h => hprime p (List.mem_toFinset.mp h)
  have hsq : Squarefree (∏ p∈ps.toFinset,p) := by
    apply Finset.squarefree_prod_of_pairwise_isCoprime
    · intro p hpp q hqq hpq
      simp only [← Nat.coprime_iff_isRelPrime]
      exact (Nat.coprime_primes (hprimeF p hpp) (hprimeF q hqq)).mpr hpq
    · intro p hpp
      exact (hprimeF p hpp).squarefree
  have hfac : ps.prod.primeFactors=ps.toFinset := by
    rw [← he]
    exact ErdosInverseCounts.primeFactors_product ps.toFinset hprimeF
  refine ⟨hpos,by rwa [he] at hsq,?_⟩
  intro p hpf
  rw [hfac] at hpf
  exact ((mem_sourcePrimeSet (zero_lt_one.trans hw) htop p).mp (hp p (List.mem_toFinset.mp hpf))).2.1

theorem reference_word_product_data {w top : ℝ} (hw : 1 < w) (htop : w < top) (i : Side) (r : ℝ) (ps : List ℕ)
    (hp : ps ∈ referencePrefixes w (sourcePrimeSet w top) i r) :
    0 < ps.prod ∧ Squarefree ps.prod ∧ ∀ p∈ps.prod.primeFactors,w<(p:ℝ) := by
  classical
  have hh := mem_decreasingPrefixes.mp (Finset.mem_filter.mp hp).1
  exact source_word_product_data hw htop ps hh.1 hh.2
end NumberTheoryLean.SourcePrimeProductData


end Erdos970

end OAI
