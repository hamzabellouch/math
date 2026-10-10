import OAI.NumberTheory.CubicMoment.Estimates.DivisorNoncubeIdentity
import OAI.NumberTheory.CubicMoment.Estimates.DivisorCubeTerm

namespace OAI

/-! The coprime component of the square-divisor variance, with its
literal lattice Poisson formula and its vanishing zero frequency. -/
noncomputable section
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

theorem coprimeDispersionGram_poisson_lattice (S : Finset Eisenstein)
    (hS : ∀ a ∈ S, primary a ∧ Squarefree a)
    (β : Eisenstein → ℂ) (u : ℝ) (W : ℝ → ℂ)
    (hW : HasCompactSupport W) (hW' : ContDiff ℝ ∞ W) {A : ℝ} (hA : 0 < A) :
    coprimeDispersionGram S β u W A =
      ∑' h : Eisenstein, finitePoissonContribution S {h} β u W A := by
  let F := fun (a b h : Eisenstein) => if IsCoprime a b then
    (β a*normTwist u a)*star (β b*normTwist u b)*
      (A/(9*Real.sqrt (norm (b*a))):ℝ)*gramDualTerm b a W A h else 0
  have hF (a b : Eisenstein) (ha : a ∈ S) (hb : b ∈ S) : Summable (F a b) := by
    by_cases hab : IsCoprime a b
    · exact (by
        simpa only [F,ite_eq_left hab] using
          (summable_gramDualTerm (hS b hb).1 (hS a ha).1 W hW hW' hA).mul_left
            ((β a*normTwist u a)*star (β b*normTwist u b)*(A/(9*Real.sqrt (norm (b*a))):ℝ)))
    · simp only [F,ite_eq_right hab]
      exact summable_zero
  have hswap : (∑' h : Eisenstein, finitePoissonContribution S {h} β u W A) =
      ∑ a ∈ S, ∑ b ∈ S, ∑' h : Eisenstein, F a b h := by
    simp only [finitePoissonContribution,Finset.sum_singleton]
    change (∑' h : Eisenstein, ∑ a ∈ S, ∑ b ∈ S, F a b h) = _
    rw [Summable.tsum_finsetSum (fun a ha => summable_sum (fun b hb => hF a b ha hb))]
    apply Finset.sum_congr rfl
    intro a ha
    exact Summable.tsum_finsetSum (fun b hb => hF a b ha hb)
  rw [hswap]
  unfold coprimeDispersionGram
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  by_cases hab : IsCoprime a b
  · simp only [ite_eq_left hab,F]
    rw [dispersion_pair_poisson (hS a ha).1 (hS b hb).1 (hS a ha).2 (hS b hb).2
      hab β u W hW hW' hA,tsum_mul_left]
    simp only [star_mul]
    ring
  · simp only [ite_eq_right hab,F,tsum_zero]

def divisorCoprimeDispersionGram (d : Eisenstein) (S : Finset Eisenstein)
    (β : Eisenstein → ℂ) (u : ℝ) (W : ℝ → ℂ) (A : ℝ) : ℂ :=
  coprimeDispersionGram S (divisorTwistedCoefficient d β) u W (A/(norm d)^2)

theorem divisorCoprimeDispersionGram_poisson {d : Eisenstein} (hd : d ≠ 0)
    (S : Finset Eisenstein) (hS : ∀ a ∈ S, primary a ∧ Squarefree a)
    (β : Eisenstein → ℂ) (u : ℝ) (W : ℝ → ℂ)
    (hW : HasCompactSupport W) (hW' : ContDiff ℝ ∞ W) {A : ℝ} (hA : 0 < A) :
    divisorCoprimeDispersionGram d S β u W A =
      ∑' h : Eisenstein, finiteDivisorPoissonContribution d S {h} β u W A := by
  have hdN := norm_pos_of_ne_zero hd
  rw [divisorCoprimeDispersionGram,coprimeDispersionGram_poisson_lattice S hS
    _ u W hW hW' (show 0 < A/(norm d)^2 by positivity)]
  apply tsum_congr
  intro h
  exact (finiteDivisorPoissonContribution_twist d S {h} β u W A).symm

lemma finiteDivisorPoissonContribution_zero (d : Eisenstein) (S : Finset Eisenstein)
    (hS : ∀ a ∈ S, primary a ∧ Squarefree a ∧ a ≠ 1)
    (β : Eisenstein → ℂ) (u : ℝ) (W : ℝ → ℂ) (A : ℝ) :
    finiteDivisorPoissonContribution d S {0} β u W A = 0 := by
  simp only [finiteDivisorPoissonContribution,Finset.sum_singleton]
  apply Finset.sum_eq_zero
  intro a ha
  apply Finset.sum_eq_zero
  intro b hb
  by_cases hab : IsCoprime a b
  · have hne : b ≠ a := by
      intro hba
      exact (hS a ha).2.2 (primary_unit_eq_one (isCoprime_self.mp (hba ▸ hab)) (hS a ha).1)
    rw [ite_eq_left hab,gramDualTerm_zero (hS b hb).1 (hS a ha).1
      (hS b hb).2.1 (hS a ha).2.1 hab.symm hne W (A/(norm d)^2)]
    ring
  · exact ite_eq_right hab

end CubicFirstMoment

end

end OAI
