import OAI.NumberTheory.Ostmann.QuadraticCenter.AmplifierExpansion
import OAI.NumberTheory.Ostmann.QuadraticCenter.MomentWeight

namespace OAI

noncomputable section
namespace Ostmann.QuadraticCenter
open scoped BigOperators

theorem subset_modulus_dvd {ι : Type*} [Fintype ι] (p : ι → ℕ) (U : Finset ι) :
    (∏ i : U, p i) ∣ ∏ i, p i := by
  classical
  rw [Finset.prod_coe_sort]
  exact Finset.prod_dvd_prod_of_subset _ _ p (Finset.subset_univ U)

theorem summable_subset_jacobi_cutoff {ι : Type*} [Fintype ι]
    (p : ι → ℕ) [∀ i, NeZero (p i)]
    (hcop : Pairwise (fun i j => (p i).Coprime (p j)))
    (S : ∀ i, Finset (ZMod (p i))) (U : Finset ι) (q : ℕ) (t : ℤ)
    {X : ℝ} (hX : 0 < X) :
    Summable (fun n : ℤ => (jacobiSym (n - t) q : ℂ) *
      subsetCenteredProduct p hcop S U (n : ZMod (∏ i : U, p i)) *
        SchwartzCutoff.psi ((n : ℝ) / X)) := by
  apply (summable_scaled_cutoff_norm hX).of_norm_bounded
  intro n
  have hJ : ‖(jacobiSym (n - t) q : ℂ)‖ ≤ 1 := by
    rcases jacobiSym.trichotomy (n - t) q with h | h | h <;> simp [h]
  have hF : ‖subsetCenteredProduct p hcop S U (n : ZMod (∏ i : U, p i))‖ ≤ 1 :=
    norm_centeredProduct_le_one (fun i : U => p i) (subset_pairwise_coprime p hcop U)
      (fun i => S i) _
  rw [norm_mul, norm_mul]
  calc
    _ ≤ (1 : ℝ) * 1 * ‖SchwartzCutoff.psi ((n : ℝ) / X)‖ := by gcongr
    _ = _ := by ring

theorem amplified_transform_subset_expansion {ι : Type*} [Fintype ι]
    (p : ι → ℕ) [∀ i, NeZero (p i)]
    (hcop : Pairwise (fun i j => (p i).Coprime (p j)))
    (S : ∀ i, Finset (ZMod (p i))) (lam : ℝ) (q : ℕ) (t : ℤ)
    {X : ℝ} (hX : 0 < X) :
    (∑' n : ℤ, (jacobiSym (n - t) q : ℂ) *
      (amplifier p hcop S lam (n : ZMod (∏ i, p i)) : ℂ) *
        SchwartzCutoff.psi ((n : ℝ) / X)) =
      ∑ U : Finset ι, (lam : ℂ) ^ U.card *
        ∑' n : ℤ, (jacobiSym (n - t) q : ℂ) *
          subsetCenteredProduct p hcop S U (n : ZMod (∏ i : U, p i)) *
            SchwartzCutoff.psi ((n : ℝ) / X) := by
  classical
  calc
    _ = ∑' n : ℤ, ∑ U : Finset ι, (lam : ℂ) ^ U.card *
        ((jacobiSym (n - t) q : ℂ) *
          subsetCenteredProduct p hcop S U (n : ZMod (∏ i : U, p i)) *
            SchwartzCutoff.psi ((n : ℝ) / X)) := by
      apply tsum_congr
      intro n
      rw [amplifier_subset_expansion, Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro U hU
      ring
    _ = ∑ U : Finset ι, ∑' n : ℤ, (lam : ℂ) ^ U.card *
        ((jacobiSym (n - t) q : ℂ) *
          subsetCenteredProduct p hcop S U (n : ZMod (∏ i : U, p i)) *
            SchwartzCutoff.psi ((n : ℝ) / X)) :=
      Summable.tsum_finsetSum (fun U _ =>
        (summable_subset_jacobi_cutoff p hcop S U q t hX).mul_left _)
    _ = _ := by simp only [tsum_mul_left]

end Ostmann.QuadraticCenter

end

end OAI
