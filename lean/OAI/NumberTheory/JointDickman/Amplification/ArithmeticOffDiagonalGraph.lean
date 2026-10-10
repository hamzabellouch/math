import OAI.NumberTheory.JointDickman.Counting.GraphCoefficientSupport

namespace OAI

/-! # Exact graph representation of the full off-diagonal energy -/

namespace JointDickman
open Finset Filter
open scoped Topology

open Classical in
noncomputable def arithmeticOffDiagonalGraph (B L : ℕ) (τ C : ℝ)
    (T N : ℕ) (F : ℕ → ℂ) : ℝ :=
  (∑ D ∈ (auxiliaryPrimes B).powerset, ∑ A ∈ (auxiliaryPrimes B).powerset,
    ∑ E ∈ (auxiliaryPrimes B).powerset, if GraphCoefficientAdmissible T D A E then
      ∑ n ∈ divisorEdgeNew (∏ p ∈ A, p) (∏ p ∈ E, p) (∏ p ∈ D, p) N (coefficientPairLag D A E),
        arithmeticGraphPairWeight B L τ C (amplificationOuterWeight B) (amplificationInnerWeight T)
          (∏ p ∈ A, p) (∏ p ∈ E, p) (∏ p ∈ D, p) (coefficientPairLag D A E) n *
          (star (F n) * F ((n : ℤ)+coefficientPairLag D A E).toNat).re
      else 0) / (N : ℝ)

/-- The original off-diagonal energy equals the arithmetic graph, including
its actual coefficient/residue weights and exact finite endpoints. -/
theorem firstFormOffDiagonal_graph (B L : ℕ) (τ C : ℝ) (T N : ℕ)
    (hT : T ≤ auxiliaryCutoff B) (F : ℕ → ℂ)
    (hF : ∀ A ∈ (auxiliaryPrimes B).powerset, ∀ n, F ((∏ p ∈ A, p)*n) = F n) :
    firstFormOffDiagonal B L τ C (amplificationOuterWeight B) (amplificationInnerWeight T)
      (fun m => F (m+1)) N = arithmeticOffDiagonalGraph B L τ C T N F := by
  classical
  rw [firstFormOffDiagonal_eq_pairSum]
  unfold arithmeticOffDiagonalGraph
  congr 1
  apply sum_congr rfl
  intro D hD
  apply sum_congr rfl
  intro A hA
  apply sum_congr rfl
  intro E hE
  have hp (S : Finset ℕ) (hS : S ∈ (auxiliaryPrimes B).powerset) : 0 < ∏ p ∈ S, p :=
    prod_pos (fun p hp => (auxiliaryPrimes_prime B p (mem_powerset.mp hS hp)).pos)
  by_cases hg : GraphCoefficientAdmissible T D A E
  · rw [ite_eq_left hg,ite_eq_right hg.1]
    exact firstFormPairEnergy_graph τ C (amplificationOuterWeight B) (amplificationInnerWeight T)
      (hp A hA) (hp E hE) (hp D hD) hg.2.2.2.1 hg.2.2.2.2 N F (hF A hA) (hF E hE) (hF D hD)
  · rw [ite_eq_right hg]
    by_cases hAE : A = E
    · rw [ite_eq_left hAE]
    · rw [ite_eq_right hAE]
      by_contra hn
      exact hg (nonzero_pairEnergy_admissible τ C (amplificationOuterWeight B)
        (fun m => F (m+1)) N (mem_powerset.mp hD) (mem_powerset.mp hA) (mem_powerset.mp hE) hAE hT hn)

/-- The exact graph identity for the moving centered second bin label. -/
theorem centered_binLabel_offDiagonal_graph {ι : Type*} [Fintype ι]
    (J : ℕ) (hJ : 0 < J) (k : ι → ℕ) (hk : ∀ i, 1 ≤ k i)
    (z : ι → ℂ) (μ : ℂ) (B L : ℕ) (τ C : ℝ) (T : ℕ) (hT : T ≤ auxiliaryCutoff B) :
    ∀ᶠ N : ℕ in atTop,
      firstFormOffDiagonal B L τ C (amplificationOuterWeight B) (amplificationInnerWeight T)
        (fun m => movingBinLabel J k z N (m+1)-μ) N =
      arithmeticOffDiagonalGraph B L τ C T N (fun n => movingBinLabel J k z N n-μ) := by
  filter_upwards [centered_movingBinLabel_invariant J hJ k hk z μ B] with N hN
  exact firstFormOffDiagonal_graph B L τ C T N hT
    (fun n => movingBinLabel J k z N n-μ) hN

end JointDickman

end OAI
