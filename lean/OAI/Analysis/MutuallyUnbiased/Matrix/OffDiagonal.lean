import OAI.Analysis.MutuallyUnbiased.Fourier.Characters

namespace OAI

noncomputable section
open scoped BigOperators ComplexConjugate

namespace MUB6

def offDiagSum {V : Type*} [AddCommMonoid V] (f : Coord → Coord → V) : V :=
  ∑ i, ∑ j ∈ Finset.univ.erase i, f i j

theorem offDiagSum_add_diag {V : Type*} [AddCommMonoid V] (f : Coord → Coord → V) :
    offDiagSum f + (∑ i, f i i) = ∑ i, ∑ j, f i j := by
  rw [offDiagSum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  exact Finset.sum_erase_add _ _ (Finset.mem_univ i)

theorem offDiagSum_sum {V ι : Type*} [AddCommMonoid V] [Fintype ι]
    (f : Coord → Coord → ι → V) :
    offDiagSum (fun i j => ∑ k, f i j k) =
      ∑ k, offDiagSum (fun i j => f i j k) := by
  unfold offDiagSum
  calc
    _ = ∑ i, ∑ k, ∑ j ∈ Finset.univ.erase i, f i j k := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_comm]
    _ = _ := Finset.sum_comm

theorem offDiagSum_mul (c : ℂ) (f : Coord → Coord → ℂ) :
    offDiagSum (fun i j => c * f i j) = c * offDiagSum f := by
  simp only [offDiagSum, Finset.mul_sum]

theorem offDiagSum_congr {V : Type*} [AddCommMonoid V]
    {f g : Coord → Coord → V} (h : ∀ i j, i ≠ j → f i j = g i j) :
    offDiagSum f = offDiagSum g := by
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j hj
  exact h i j (Ne.symm (Finset.mem_erase.mp hj).1)

@[simp] theorem offDiagSum_zero {V : Type*} [AddCommMonoid V] :
    offDiagSum (fun _ _ => (0 : V)) = 0 := by simp [offDiagSum]

theorem sum_mul_conj (z : Coord → ℂ) :
    (∑ i, ∑ j, z i * conj (z j)) = (Complex.normSq (∑ i, z i) : ℂ) := by
  rw [← Complex.mul_conj, map_sum]
  simp only [Finset.sum_mul, Finset.mul_sum]
  exact Finset.sum_comm

end MUB6

end

end OAI
