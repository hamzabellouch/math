import OAI.NumberTheory.Ostmann.QuadraticCenter.BiasedMoment
import OAI.NumberTheory.Ostmann.QuadraticCenter.MomentWeight

namespace OAI

noncomputable section
namespace Ostmann.QuadraticCenter
open scoped BigOperators

def cutoffLower : ℝ := Classical.choose SchwartzCutoff.psi_uniform_lower

theorem cutoffLower_pos : 0 < cutoffLower :=
  (Classical.choose_spec SchwartzCutoff.psi_uniform_lower).1

theorem cutoffLower_le {x : ℝ} (hx : |x| ≤ 1) : cutoffLower ≤ (SchwartzCutoff.psi x).re :=
  (Classical.choose_spec SchwartzCutoff.psi_uniform_lower).2 x hx

theorem amplified_moment_lower {ι : Type*} [Fintype ι]
    (p : ι → ℕ) [∀ i, NeZero (p i)]
    (hcop : Pairwise (fun i j => (p i).Coprime (p j)))
    (S : ∀ i, Finset (ZMod (p i))) {lam X c δ : ℝ}
    (hlam : 0 ≤ lam) (hlam1 : lam < 1) (hX : 0 < X) (hc : 0 ≤ c) (hδ : 0 ≤ δ)
    (hbal : ∀ i, Supply.density (S i) ≤ 1 - c)
    (A : Finset ℤ) (hA : 0 < A.card) (P : Finset ℕ) (hP : 0 < P.card)
    (ε t : ℕ → ℤ) (hε : ∀ r ∈ P, ε r = -1 ∨ ε r = 1)
    (hwindow : ∀ a ∈ A, |(a : ℝ) / X| ≤ 1)
    (hsupport : ∀ a ∈ A, ∀ i,
      ZMod.prodEquivPi p hcop (a : ZMod (∏ j, p j)) i ∈ S i)
    (hbias : ∀ r ∈ P,
      δ ≤ (∑ a ∈ A, ((ε r * jacobiSym (a - t r) r : ℤ) : ℝ)) / A.card)
    {k : ℕ} (hk : Even k) :
    cutoffLower * (1 + lam * c) ^ Fintype.card ι * A.card * δ ^ k ≤
      ∑' n : ℤ, amplifiedMomentTerm p hcop S lam X P ε t k n := by
  have hJ := translated_jacobi_biased_moment A P hA hP ε t hδ hbias hk
  change (A.card : ℝ) * δ ^ k ≤ ∑ a ∈ A, orientedQuadraticAverage P ε t a ^ k at hJ
  have hC : 0 ≤ cutoffLower * (1 + lam * c) ^ Fintype.card ι := by
    exact mul_nonneg cutoffLower_pos.le (pow_nonneg (by positivity) _)
  have hfinite : cutoffLower * (1 + lam * c) ^ Fintype.card ι * A.card * δ ^ k ≤
      ∑ a ∈ A, amplifiedMomentTerm p hcop S lam X P ε t k a := by
    calc
      _ = (cutoffLower * (1 + lam * c) ^ Fintype.card ι) * ((A.card : ℝ) * δ ^ k) := by ring
      _ ≤ (cutoffLower * (1 + lam * c) ^ Fintype.card ι) *
          ∑ a ∈ A, orientedQuadraticAverage P ε t a ^ k := mul_le_mul_of_nonneg_left hJ hC
      _ = ∑ a ∈ A, (cutoffLower * (1 + lam * c) ^ Fintype.card ι) *
          orientedQuadraticAverage P ε t a ^ k := by rw [Finset.mul_sum]
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro a ha
        unfold amplifiedMomentTerm
        apply mul_le_mul_of_nonneg_right _ (hk.pow_nonneg _)
        exact mul_le_mul (cutoffLower_le (hwindow a ha))
          (amplifier_lower_on_support p hcop S hlam hc hbal _ (hsupport a ha))
          (pow_nonneg (by positivity) _) (SchwartzCutoff.psi_nonneg _)
  exact hfinite.trans (Summable.sum_le_tsum A
    (fun n _ => amplifiedMomentTerm_nonneg p hcop S hlam hlam1 X P ε t hk n)
    (amplifiedMoment_summable p hcop S hlam hlam1 hX P hP ε t hε hk))

end Ostmann.QuadraticCenter

end

end OAI
