import OAI.NumberTheory.Jacobsthal.Sieve.OriginalCofactorSums

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970


namespace NumberTheoryLean.TwoPrimeObservableSum
open ErdosCofactorChoices SingletonBinSelection TwoSingletonBins OriginalCofactorSums

attribute [local instance] Classical.propDecidable

noncomputable def pickedPrime {n : ℕ} (f : Fin n → Finset ℕ) (i : Fin n) : ℕ := (f i).toList.getLastD 0
noncomputable def eraseTwoSelection {n : ℕ} (f : Fin n → Finset ℕ) (i j : Fin n) : Fin n → Finset ℕ :=
  eraseSelection (eraseSelection f i) j

theorem picked_fillTwo {n : ℕ} (f : Fin n → Finset ℕ) (i j : Fin n) (hij : i ≠ j) (p u : ℕ) :
    pickedPrime (fillTwo f i j p u) i=p ∧ pickedPrime (fillTwo f i j p u) j=u := by
  simp [pickedPrime,fillTwo,fillSelection,Ne.symm hij]

theorem erase_filled_two {n : ℕ} (f : Fin n → Finset ℕ) (i j : Fin n)
    (hi : f i=∅) (hj : f j=∅) (p u : ℕ) :
    eraseTwoSelection (fillTwo f i j p u) i j=f := by
  funext k
  by_cases hki : k=i
  · subst k; simp [eraseTwoSelection,eraseSelection,hi]
  · by_cases hkj : k=j
    · subst k; simp [eraseTwoSelection,eraseSelection,hj]
    · simp [eraseTwoSelection,eraseSelection,fillTwo,fillSelection,hki,hkj]

theorem full_two_prime_sum {n : ℕ} (P : Fin n → Finset ℕ) (m : Fin n → ℕ)
    (hP : ∀ i,∀ p ∈ P i,p.Prime) (hd : Pairwise (fun i j => Disjoint (P i) (P j)))
    (i j : Fin n) (hij : i ≠ j) (hi : m i=1) (hj : m j=1) (G : ℕ → ℕ → ℕ → ℝ) :
    (∑ f ∈ selections P m,(selectionProduct f:ℝ)⁻¹*
      G (pickedPrime f i) (pickedPrime f j) (selectionProduct (eraseTwoSelection f i j)))=
    ∑ p ∈ P i,∑ u ∈ P j,∑ q ∈ cofactorChoices P (eraseTwo m i j),
      ((p:ℝ)⁻¹*(u:ℝ)⁻¹*(q:ℝ)⁻¹)*G p u q := by
  rw [two_singleton_weighted_sum P m i j hij hi hj]
  rw [← two_prime_cofactor_sum P m hP hd i j G]
  apply Finset.sum_congr rfl
  intro p _hp
  apply Finset.sum_congr rfl
  intro u _hu
  apply Finset.sum_congr rfl
  intro f hf
  have hm := (mem_selections P _ f).mp hf
  have hei : f i=∅ := Finset.card_eq_zero.mp ((hm i).2.trans (eraseTwo_zero m i j).1)
  have hej : f j=∅ := Finset.card_eq_zero.mp ((hm j).2.trans (eraseTwo_zero m i j).2)
  rw [(picked_fillTwo f i j hij p u).1,(picked_fillTwo f i j hij p u).2,erase_filled_two f i j hei hej p u]
end NumberTheoryLean.TwoPrimeObservableSum


end Erdos970

end OAI
