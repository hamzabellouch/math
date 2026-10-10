import OAI.NumberTheory.JointDickman.Arithmetic.BrunBlocks

namespace OAI

/-! # Finite block upper sieve with unit remainder coefficients -/
namespace JointDickman
open Finset

 theorem avoidsSelected_antitone {P Q E : Finset ℕ} (hQP : Q ⊆ P) :
    avoidsSelected P E ≤ avoidsSelected Q E := by
  classical
  by_cases h : Disjoint P E
  · simp [avoidsSelected,h,h.mono_left hQP]
  · simp only [avoidsSelected,h,ite_false]
    split_ifs <;> norm_num

 theorem brunBlock_population_sum {X ι : Type*} [Fintype X] [Fintype ι]
    (P : ι → Finset ℕ) (r : ι → ℕ) (E : X → Finset ℕ) (w : X → ℝ) :
    (∑ x, w x * ∏ i, brunTruncation (P i ∩ E x) (2*r i)) =
      ∑ D ∈ brunBlockChoices P r, brunBlockSign D * sieveIntersection E w (brunBlockUnion D) := by
  classical
  simp_rw [brunBlock_expansion,mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro D _
  rw [sieveIntersection,mul_sum]
  apply sum_congr rfl
  intro x _
  split_ifs <;> ring

 theorem brunBlock_population_bound {X ι : Type*} [Fintype X] [Fintype ι]
    (Q : Finset ℕ) (P : ι → Finset ℕ) (r : ι → ℕ)
    (hP : Pairwise (fun i j => Disjoint (P i) (P j))) (hPQ : ∀ i, P i ⊆ Q)
    (E : X → Finset ℕ) (w : X → ℝ) (hw : ∀ x, 0 ≤ w x)
    (M z : ℝ) (g : ℕ → ℝ)
    (hcut : ∀ D ∈ brunBlockChoices P r, (∏ p ∈ brunBlockUnion D, p : ℕ) ≤ z) :
    (∑ x, w x * avoidsSelected Q (E x)) ≤
      M*(∏ i, brunMean (P i) g (r i)) +
      ∑ D ∈ Q.powerset.filter (fun D => (∏ p ∈ D, p : ℕ) ≤ z), |sieveRemainder E w M g D| := by
  classical
  have hUQ : brunBlockUnion P ⊆ Q := by
    intro p hp
    obtain ⟨i,_,hi⟩ := mem_biUnion.mp hp
    exact hPQ i hi
  calc
    _ ≤ ∑ x, w x * ∏ i, brunTruncation (P i ∩ E x) (2*r i) := by
      apply sum_le_sum
      intro x _
      apply mul_le_mul_of_nonneg_left _ (hw x)
      exact (avoidsSelected_antitone hUQ).trans (brunBlock_upper P r (E x))
    _ = M*(∏ i, brunMean (P i) g (r i)) +
        ∑ D ∈ brunBlockChoices P r, brunBlockSign D*sieveRemainder E w M g (brunBlockUnion D) := by
      rw [brunBlock_population_sum, ← brunBlock_main P r hP, mul_sum, ← sum_add_distrib]
      apply sum_congr rfl
      intro D _
      rw [sieveRemainder]
      ring
    _ ≤ M*(∏ i, brunMean (P i) g (r i)) +
        ∑ D ∈ brunBlockChoices P r, |sieveRemainder E w M g (brunBlockUnion D)| := by
      apply add_le_add le_rfl
      apply sum_le_sum
      intro D _
      calc
        _ ≤ |brunBlockSign D*sieveRemainder E w M g (brunBlockUnion D)| := le_abs_self _
        _ = _ := by rw [abs_mul,brunBlockSign_abs,one_mul]
    _ ≤ _ := by
      apply add_le_add le_rfl
      apply sum_le_sum_of_injOn brunBlockUnion (brunBlockUnion_injOn P r hP)
      · intro F hF
        obtain ⟨D,hD,rfl⟩ := mem_image.mp hF
        apply mem_filter.mpr
        refine ⟨mem_powerset.mpr ?_,hcut D hD⟩
        intro p hp
        obtain ⟨i,_,hi⟩ := mem_biUnion.mp hp
        exact hPQ i (((brunBlockChoices_mem P r D).mp hD i).1 hi)
      · intro D _
        exact le_rfl
      · intro D _ _
        exact abs_nonneg _

end JointDickman

end OAI
