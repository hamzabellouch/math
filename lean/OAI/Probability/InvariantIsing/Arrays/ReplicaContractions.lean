import OAI.Probability.InvariantIsing.Arrays.CoordinateWard

namespace OAI

/-!
# Finite replica contractions in the spectral Ward calculation

The sums over two spectral coordinate groups contract into products of
projected overlaps. These are exact finite identities, with no symmetry or
full-support requirement on the deterministic spin prior.
-/

noncomputable section

open IsingPerceptron
open scoped BigOperators

namespace InvariantIsing

variable {S ι : Type*} [Fintype S]

/-- Independent replicas sampled from the same finite Gibbs law. -/
def gibbsPairAverage (w H : S → ℝ) (A : S → S → ℝ) : ℝ :=
  ∑ σ, ∑ τ, finiteGibbs w H σ * finiteGibbs w H τ * A σ τ

/-- Unnormalized projected overlap; division by N is applied after contraction. -/
def blockOverlap (x : S → ι → ℝ) (I : Finset ι) (σ τ : S) : ℝ :=
  ∑ i ∈ I, x σ i * x τ i

lemma gibbsAverage_finset_sum (w H : S → ℝ) (I : Finset ι) (A : ι → S → ℝ) :
    gibbsAverage w H (fun σ => ∑ i ∈ I, A i σ) = ∑ i ∈ I, gibbsAverage w H (A i) := by
  simp only [gibbsAverage, Finset.mul_sum]
  rw [Finset.sum_comm]

lemma gibbsAverage_sub (w H A B : S → ℝ) :
    gibbsAverage w H (fun σ => A σ - B σ) = gibbsAverage w H A - gibbsAverage w H B := by
  simp only [gibbsAverage, mul_sub, Finset.sum_sub_distrib]

lemma gibbsPairAverage_finset_sum (w H : S → ℝ) (I : Finset ι) (A : ι → S → S → ℝ) :
    gibbsPairAverage w H (fun σ τ => ∑ i ∈ I, A i σ τ) =
      ∑ i ∈ I, gibbsPairAverage w H (A i) := by
  simp only [gibbsPairAverage, Finset.mul_sum]
  trans ∑ σ, ∑ i ∈ I, ∑ τ, finiteGibbs w H σ * finiteGibbs w H τ * A i σ τ
  · apply Finset.sum_congr rfl
    intro σ _
    rw [Finset.sum_comm]
  · rw [Finset.sum_comm]

lemma gibbsAverage_mul_gibbsAverage (w H A B : S → ℝ) :
    gibbsAverage w H A * gibbsAverage w H B =
      gibbsPairAverage w H (fun σ τ => A σ * B τ) := by
  simp only [gibbsAverage, gibbsPairAverage, Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro σ _
  apply Finset.sum_congr rfl
  intro τ _
  ring

/-- The direct Hamiltonian term contracts into a one-replica diagonal product. -/
lemma coordinate_fourth_contraction (w H : S → ℝ) (x : S → ι → ℝ) (I J : Finset ι) :
    (∑ i ∈ I, ∑ j ∈ J, gibbsAverage w H (fun σ => (x σ i * x σ j) ^ 2)) =
      gibbsAverage w H (fun σ => blockOverlap x I σ σ * blockOverlap x J σ σ) := by
  simp_rw [← gibbsAverage_finset_sum]
  congr 1
  funext σ
  simp only [blockOverlap, Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- The Gibbs-ratio subtraction contracts into a two-replica overlap product. -/
lemma coordinate_mean_square_contraction (w H : S → ℝ) (x : S → ι → ℝ) (I J : Finset ι) :
    (∑ i ∈ I, ∑ j ∈ J, gibbsAverage w H (fun σ => x σ i * x σ j) ^ 2) =
      gibbsPairAverage w H (fun σ τ => blockOverlap x I σ τ * blockOverlap x J σ τ) := by
  simp only [pow_two]
  simp_rw [gibbsAverage_mul_gibbsAverage]
  simp_rw [← gibbsPairAverage_finset_sum]
  congr 1
  funext σ τ
  simp only [blockOverlap, Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma coordinate_difference_contraction (w H : S → ℝ) (x : S → ι → ℝ) (I J : Finset ι) :
    (∑ i ∈ I, ∑ j ∈ J, gibbsAverage w H (fun σ => x σ j ^ 2 - x σ i ^ 2)) =
      (I.card : ℝ) * gibbsAverage w H (fun σ => blockOverlap x J σ σ) -
        (J.card : ℝ) * gibbsAverage w H (fun σ => blockOverlap x I σ σ) := by
  simp_rw [gibbsAverage_sub]
  simp only [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum]
  have hI : gibbsAverage w H (fun σ => blockOverlap x I σ σ) =
      ∑ i ∈ I, gibbsAverage w H (fun σ => x σ i ^ 2) := by
    simp only [blockOverlap, ← pow_two]
    exact gibbsAverage_finset_sum w H I _
  have hJ : gibbsAverage w H (fun σ => blockOverlap x J σ σ) =
      ∑ j ∈ J, gibbsAverage w H (fun σ => x σ j ^ 2) := by
    simp only [blockOverlap, ← pow_two]
    exact gibbsAverage_finset_sum w H J _
  rw [hI, hJ]

end InvariantIsing

end

end OAI
