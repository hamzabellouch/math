import OAI.NumberTheory.Jacobsthal.Partitions.TwoSingletonBins

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970


namespace NumberTheoryLean.OriginalCofactorSums
open ErdosCofactorChoices TwoSingletonBins

attribute [local instance] Classical.propDecidable

theorem cofactor_sum {n : ℕ} (P : Fin n → Finset ℕ) (m : Fin n → ℕ)
    (hP : ∀ i,∀ p ∈ P i,p.Prime) (hd : Pairwise (fun i j => Disjoint (P i) (P j)))
    (G : ℕ → ℝ) :
    (∑ f ∈ selections P m,G (selectionProduct f))=∑ q ∈ cofactorChoices P m,G q := by
  symm
  rw [cofactorChoices,Finset.sum_image]
  exact fun f hf g hg he => selectionProduct_injOn P m hP hd hf hg he

theorem two_prime_cofactor_sum {n : ℕ} (P : Fin n → Finset ℕ) (m : Fin n → ℕ)
    (hP : ∀ i,∀ p ∈ P i,p.Prime) (hd : Pairwise (fun i j => Disjoint (P i) (P j)))
    (i j : Fin n)
    (G : ℕ → ℕ → ℕ → ℝ) :
    (∑ p ∈ P i,∑ u ∈ P j,∑ f ∈ selections P (eraseTwo m i j),
      ((p:ℝ)⁻¹*(u:ℝ)⁻¹*(selectionProduct f:ℝ)⁻¹)*G p u (selectionProduct f))=
    ∑ p ∈ P i,∑ u ∈ P j,∑ q ∈ cofactorChoices P (eraseTwo m i j),
      ((p:ℝ)⁻¹*(u:ℝ)⁻¹*(q:ℝ)⁻¹)*G p u q := by
  apply Finset.sum_congr rfl
  intro p _hp
  apply Finset.sum_congr rfl
  intro u _hu
  exact cofactor_sum P (eraseTwo m i j) hP hd (fun q => ((p:ℝ)⁻¹*(u:ℝ)⁻¹*(q:ℝ)⁻¹)*G p u q)
end NumberTheoryLean.OriginalCofactorSums


end Erdos970

end OAI
