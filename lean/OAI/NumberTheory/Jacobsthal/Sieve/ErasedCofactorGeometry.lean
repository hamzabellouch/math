import OAI.NumberTheory.Jacobsthal.Partitions.SourceDenseCellContradiction
import OAI.NumberTheory.Jacobsthal.Paths.FiniteBoxWordMass

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace ErdosVarianceWeighted
open NumberTheoryLean ErdosCofactorChoices ErdosSubsetWord SingletonBinSelection ErdosInverseRefinement
  LogarithmicBinScale LogarithmicBinLabels LogarithmicBinPartition LogarithmicBinEndpoints
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

theorem erased_cofactor_arithmetic {w top xi : ℝ} (hw : 1 < w) (htop : w < top) (hxi : 0 < xi)
    (m : Fin (binCount w top xi) → ℕ) (i : Fin (binCount w top xi))
    (f : Fin (binCount w top xi) → Finset ℕ)
    (hf : f ∈ selections (globalBins w top xi) (eraseMultiplicity m i)) :
    Squarefree (selectionProduct f) ∧ (∀ t ∈ (selectionProduct f).primeFactors,w < (t : ℝ)) ∧
      ∀ p ∈ globalBins w top xi i,(selectionProduct f).Coprime p := by
  let P := globalBins w top xi
  have hP : ∀ j,∀ p ∈ P j,p.Prime := fun j p hp => (bin_prime_in_source (by linarith) htop hxi j hp).1
  have hd : Pairwise (fun j k => Disjoint (P j) (P k)) :=
    fun j k hjk => bins_pairwise_disjoint (by linarith) htop hxi j k hjk
  have hq : selectionProduct f ∈ cofactorChoices P (eraseMultiplicity m i) :=
    Finset.mem_image.mpr ⟨f,hf,rfl⟩
  refine ⟨cofactor_squarefree P _ hP hd _ hq,?_,
    cofactor_coprime_excluded_bin P _ hP hd i (by simp [eraseMultiplicity]) _ hq⟩
  intro t ht
  rw [selectionProduct_primeFactors P hP hd f (fun j => ((mem_selections P _ f).mp hf j).1)] at ht
  obtain ⟨j,_hj,htj⟩ := Finset.mem_biUnion.mp ht
  exact (bin_prime_in_source (by linarith) htop hxi j (((mem_selections P _ f).mp hf j).1 htj)).2.1

end ErdosVarianceWeighted

end

end Erdos970

end OAI
