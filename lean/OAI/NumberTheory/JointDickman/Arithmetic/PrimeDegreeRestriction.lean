import OAI.NumberTheory.JointDickman.Amplification.GeneratingDegreeExpansion

namespace OAI

/-! # Removing primes with trivial generating weight -/
namespace JointDickman
open Finset

 theorem primeGeneratingDegree_congr (P : Finset ℕ) (z w : ℕ → ℝ)
    (hz : ∀ p ∈ P, z p = w p) (N h : ℕ) :
    primeGeneratingDegree P z N h = primeGeneratingDegree P w N h := by
  classical
  unfold primeGeneratingDegree
  apply sum_congr rfl
  intro D hD
  have hsub := (mem_powersetCard.mp hD).1
  congr 1
  congr 1
  apply prod_congr rfl
  intro p hp
  rw [hz p (hsub hp)]

 theorem primeGeneratingDegree_restrict (P Q : Finset ℕ) (hQP : Q ⊆ P) (z : ℕ → ℝ)
    (hz : ∀ p ∈ P, p ∉ Q → z p = 1) (N h : ℕ) :
    primeGeneratingDegree P z N h = primeGeneratingDegree Q z N h := by
  classical
  unfold primeGeneratingDegree
  have hsub : Q.powersetCard h ⊆ P.powersetCard h := by
    intro D hD
    obtain ⟨hDQ,hDh⟩ := mem_powersetCard.mp hD
    exact mem_powersetCard.mpr ⟨hDQ.trans hQP,hDh⟩
  symm
  apply sum_subset hsub
  intro D hDP hDQ
  obtain ⟨hDP,hDh⟩ := mem_powersetCard.mp hDP
  have hnsub : ¬D ⊆ Q := fun hsub => hDQ (mem_powersetCard.mpr ⟨hsub,hDh⟩)
  obtain ⟨p,hp,hpQ⟩ := not_subset.mp hnsub
  have he : ∏ q ∈ D, (z q-1) = 0 :=
    prod_eq_zero hp (by rw [hz p (hDP hp) hpQ]; ring)
  simp [he]

end JointDickman

end OAI
