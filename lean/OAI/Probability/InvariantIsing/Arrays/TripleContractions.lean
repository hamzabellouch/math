import OAI.Probability.InvariantIsing.Core.PairGibbs

namespace OAI

/-! Replica contractions for the off-diagonal spectral Ward equation. -/

noncomputable section

open IsingPerceptron
open scoped BigOperators

namespace InvariantIsing

variable {S ι : Type*} [Fintype S]

def gibbsTripleAverage (w H : S → ℝ) (A : S → S → S → ℝ) : ℝ :=
  ∑ σ, ∑ τ, ∑ η, finiteGibbs w H σ * finiteGibbs w H τ * finiteGibbs w H η * A σ τ η

lemma gibbsPairAverage_mul_gibbsAverage (w H B : S → ℝ) (A : S → S → ℝ) :
    gibbsPairAverage w H A * gibbsAverage w H B =
      gibbsTripleAverage w H (fun σ τ η => A σ τ * B η) := by
  unfold gibbsPairAverage gibbsAverage gibbsTripleAverage
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro σ _
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro τ _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro η _
  ring

lemma gibbsPairAverage_sub (w H : S → ℝ) (A B : S → S → ℝ) :
    gibbsPairAverage w H (fun σ τ => A σ τ - B σ τ) =
      gibbsPairAverage w H A - gibbsPairAverage w H B := by
  simp only [gibbsPairAverage, mul_sub, Finset.sum_sub_distrib]

lemma gibbsTripleAverage_finset_sum (w H : S → ℝ) (I : Finset ι) (A : ι → S → S → S → ℝ) :
    gibbsTripleAverage w H (fun σ τ η => ∑ i ∈ I, A i σ τ η) =
      ∑ i ∈ I, gibbsTripleAverage w H (A i) := by
  simp only [gibbsTripleAverage, Finset.mul_sum]
  trans ∑ σ, ∑ τ, ∑ i ∈ I, ∑ η,
    finiteGibbs w H σ * finiteGibbs w H τ * finiteGibbs w H η * A i σ τ η
  · apply Finset.sum_congr rfl
    intro σ _
    apply Finset.sum_congr rfl
    intro τ _
    rw [Finset.sum_comm]
  · trans ∑ σ, ∑ i ∈ I, ∑ τ, ∑ η,
      finiteGibbs w H σ * finiteGibbs w H τ * finiteGibbs w H η * A i σ τ η
    · apply Finset.sum_congr rfl
      intro σ _
      rw [Finset.sum_comm]
    · rw [Finset.sum_comm]

lemma off_direct_contraction (w H : S → ℝ) (x : S → ι → ℝ)
    (I J : Finset ι) (F : S → S → ℝ) :
    (∑ i ∈ I, ∑ j ∈ J, gibbsPairAverage w H (fun σ τ =>
      x σ i * x τ j * F σ τ * (x σ i * x σ j + x τ i * x τ j))) =
      gibbsPairAverage w H (fun σ τ =>
        (blockOverlap x I σ σ * blockOverlap x J σ τ +
          blockOverlap x I σ τ * blockOverlap x J τ τ) * F σ τ) := by
  simp_rw [← gibbsPairAverage_finset_sum]
  congr 1
  funext σ τ
  simp only [blockOverlap, add_mul, Finset.sum_mul_sum]
  simp only [Finset.sum_mul, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma off_subtraction_contraction (w H : S → ℝ) (x : S → ι → ℝ)
    (I J : Finset ι) (F : S → S → ℝ) :
    (∑ i ∈ I, ∑ j ∈ J,
      gibbsPairAverage w H (fun σ τ => x σ i * x τ j * F σ τ) *
        gibbsAverage w H (fun η => x η i * x η j)) =
      gibbsTripleAverage w H (fun σ τ η =>
        blockOverlap x I σ η * blockOverlap x J τ η * F σ τ) := by
  simp_rw [gibbsPairAverage_mul_gibbsAverage, ← gibbsTripleAverage_finset_sum]
  congr 1
  funext σ τ η
  simp only [blockOverlap, Finset.sum_mul_sum]
  simp only [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma off_difference_contraction (w H : S → ℝ) (x : S → ι → ℝ)
    (I J : Finset ι) (F : S → S → ℝ) :
    (∑ i ∈ I, ∑ j ∈ J, gibbsPairAverage w H (fun σ τ =>
      (x σ j * x τ j - x σ i * x τ i) * F σ τ)) =
      (I.card : ℝ) * gibbsPairAverage w H (fun σ τ => blockOverlap x J σ τ * F σ τ) -
        (J.card : ℝ) * gibbsPairAverage w H (fun σ τ => blockOverlap x I σ τ * F σ τ) := by
  simp only [sub_mul]
  simp_rw [gibbsPairAverage_sub]
  simp only [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum]
  have hI : gibbsPairAverage w H (fun σ τ => blockOverlap x I σ τ * F σ τ) =
      ∑ i ∈ I, gibbsPairAverage w H (fun σ τ => x σ i * x τ i * F σ τ) := by
    simp only [blockOverlap, Finset.sum_mul]
    exact gibbsPairAverage_finset_sum w H I _
  have hJ : gibbsPairAverage w H (fun σ τ => blockOverlap x J σ τ * F σ τ) =
      ∑ j ∈ J, gibbsPairAverage w H (fun σ τ => x σ j * x τ j * F σ τ) := by
    simp only [blockOverlap, Finset.sum_mul]
    exact gibbsPairAverage_finset_sum w H J _
  rw [hI, hJ]

end InvariantIsing

end

end OAI
