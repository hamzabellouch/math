import OAI.NumberTheory.Ostmann.QuadraticCenter.AmplifierMass
import OAI.NumberTheory.Ostmann.QuadraticCenter.DistinctQuadraticMoment

namespace OAI

noncomputable section
namespace Ostmann.QuadraticCenter
open Ostmann.QuadraticSieve
open scoped BigOperators SchwartzMap

def orientedQuadraticAverage (P : Finset ℕ) (ε t : ℕ → ℤ) (n : ℤ) : ℝ :=
  (∑ p ∈ P, ((ε p * jacobiSym (n - t p) p : ℤ) : ℝ)) / P.card

theorem abs_orientedQuadraticAverage_le_one (P : Finset ℕ) (hP : 0 < P.card)
    (ε t : ℕ → ℤ) (hε : ∀ p ∈ P, ε p = -1 ∨ ε p = 1) (n : ℤ) :
    |orientedQuadraticAverage P ε t n| ≤ 1 := by
  have hp : (0 : ℝ) < P.card := by exact_mod_cast hP
  rw [orientedQuadraticAverage, abs_div, abs_of_pos hp, div_le_one hp]
  calc
    _ ≤ ∑ p ∈ P, |((ε p * jacobiSym (n - t p) p : ℤ) : ℝ)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _p ∈ P, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro p hp'
      rcases oriented_jacobi_trichotomy (ε p) (n - t p) p (hε p hp') with h | h | h <;>
        simp only [h] <;> norm_num
    _ = _ := by simp

theorem amplifier_le {ι : Type*} [Fintype ι] (p : ι → ℕ) [∀ i, NeZero (p i)]
    (hcop : Pairwise (fun i j => (p i).Coprime (p j)))
    (S : ∀ i, Finset (ZMod (p i))) {lam : ℝ} (hlam : 0 ≤ lam) (hlam1 : lam < 1)
    (x : ZMod (∏ i, p i)) : amplifier p hcop S lam x ≤ (1 + lam) ^ Fintype.card ι := by
  have he : (1 + lam) ^ Fintype.card ι = ∏ _i : ι, (1 + lam) := by simp
  rw [he]
  unfold amplifier
  apply Finset.prod_le_prod₀
  · intro i hi
    exact (amplifier_factor_pos (S i) hlam hlam1 _).le
  · intro i hi
    have hden := (residue_density_bounds (S i)).1
    have hc : Supply.centeredIndicator (S i) (ZMod.prodEquivPi p hcop x i) ≤ 1 := by
      unfold Supply.centeredIndicator
      split_ifs <;> linarith
    nlinarith [mul_le_mul_of_nonneg_left hc hlam]

theorem summable_scaled_cutoff_norm {X : ℝ} (hX : 0 < X) :
    Summable (fun n : ℤ => ‖SchwartzCutoff.psi ((n : ℝ) / X)‖) := by
  have hi : X⁻¹ ≠ 0 := inv_ne_zero hX.ne'
  have h := (schwartz_summable_int (dilatedSchwartz X⁻¹ hi SchwartzCutoff.psi)).norm
  simpa only [dilatedSchwartz_apply, div_eq_mul_inv, mul_comm] using h

def amplifiedMomentTerm {ι : Type*} [Fintype ι]
    (p : ι → ℕ) [∀ i, NeZero (p i)]
    (hcop : Pairwise (fun i j => (p i).Coprime (p j)))
    (S : ∀ i, Finset (ZMod (p i))) (lam X : ℝ)
    (P : Finset ℕ) (ε t : ℕ → ℤ) (k : ℕ) (n : ℤ) : ℝ :=
  (SchwartzCutoff.psi ((n : ℝ) / X)).re * amplifier p hcop S lam (n : ZMod (∏ i, p i)) *
    orientedQuadraticAverage P ε t n ^ k

theorem amplifiedMomentTerm_nonneg {ι : Type*} [Fintype ι]
    (p : ι → ℕ) [∀ i, NeZero (p i)]
    (hcop : Pairwise (fun i j => (p i).Coprime (p j)))
    (S : ∀ i, Finset (ZMod (p i))) {lam : ℝ} (hlam : 0 ≤ lam) (hlam1 : lam < 1)
    (X : ℝ) (P : Finset ℕ) (ε t : ℕ → ℤ) {k : ℕ} (hk : Even k) (n : ℤ) :
    0 ≤ amplifiedMomentTerm p hcop S lam X P ε t k n :=
  mul_nonneg (mul_nonneg (SchwartzCutoff.psi_nonneg _)
    (amplifier_pos p hcop S hlam hlam1 _).le) (hk.pow_nonneg _)

theorem amplifiedMoment_summable {ι : Type*} [Fintype ι]
    (p : ι → ℕ) [∀ i, NeZero (p i)]
    (hcop : Pairwise (fun i j => (p i).Coprime (p j)))
    (S : ∀ i, Finset (ZMod (p i))) {lam X : ℝ}
    (hlam : 0 ≤ lam) (hlam1 : lam < 1) (hX : 0 < X)
    (P : Finset ℕ) (hP : 0 < P.card) (ε t : ℕ → ℤ)
    (hε : ∀ p ∈ P, ε p = -1 ∨ ε p = 1) {k : ℕ} (hk : Even k) :
    Summable (amplifiedMomentTerm p hcop S lam X P ε t k) := by
  refine Summable.of_nonneg_of_le
    (amplifiedMomentTerm_nonneg p hcop S hlam hlam1 X P ε t hk) ?_
    ((summable_scaled_cutoff_norm hX).mul_right ((1 + lam) ^ Fintype.card ι))
  intro n
  have hpow : orientedQuadraticAverage P ε t n ^ k ≤ 1 := by
    rw [← hk.pow_abs]
    exact pow_le_one₀ (abs_nonneg _) (abs_orientedQuadraticAverage_le_one P hP ε t hε n)
  have hW := (amplifier_pos p hcop S hlam hlam1 (n : ZMod (∏ i, p i))).le
  calc
    _ ≤ (SchwartzCutoff.psi ((n : ℝ) / X)).re *
        amplifier p hcop S lam (n : ZMod (∏ i, p i)) :=
      mul_le_of_le_one_right (mul_nonneg (SchwartzCutoff.psi_nonneg _) hW) hpow
    _ ≤ _ := mul_le_mul (Complex.re_le_norm _)
      (amplifier_le p hcop S hlam hlam1 _) hW (norm_nonneg _)

end Ostmann.QuadraticCenter

end

end OAI
