import OAI.NumberTheory.Ostmann.QuadraticCenter.Amplifier
import OAI.NumberTheory.Ostmann.QuadraticCenter.WeightedPoisson
import OAI.NumberTheory.Ostmann.SchwartzCutoff

namespace OAI

namespace Ostmann.QuadraticCenter
open Ostmann.QuadraticSieve
open scoped BigOperators SchwartzMap FourierTransform

theorem cutoff_nonzero_periodic_frequency {q : ℕ} [NeZero q]
    {X : ℝ} (hX : 0 < X) (hscale : (1 : ℝ) / 4 ≤ X / q)
    {h : ℤ} (hh : h ≠ 0) : 𝓕 SchwartzCutoff.psi ((h : ℝ) * X / q) = 0 := by
  apply SchwartzCutoff.fourier_psi_zero_of_abs_ge
  have hq : (0 : ℝ) < q := by exact_mod_cast (Nat.pos_of_neZero q)
  have hh1 : (1 : ℝ) ≤ |(h : ℝ)| := by exact_mod_cast (Int.one_le_abs hh)
  calc
    (1 : ℝ) / 4 ≤ X / q := hscale
    _ ≤ |(h : ℝ)| * (X / q) := le_mul_of_one_le_left (by positivity) hh1
    _ = |(h : ℝ) * X / q| := by
      rw [abs_div, abs_mul, abs_of_pos hX, abs_of_pos hq]
      ring

theorem periodic_cutoff_mass {q : ℕ} [NeZero q] (W : ZMod q → ℝ)
    (hW : (∑ a : ZMod q, W a) = (q : ℝ))
    (X : ℝ) (hX : 0 < X) (hscale : (1 : ℝ) / 4 ≤ X / q) :
    (∑' n : ℤ, (W (n : ZMod q) : ℂ) * SchwartzCutoff.psi ((n : ℝ) / X)) =
      (X : ℂ) * 𝓕 SchwartzCutoff.psi 0 := by
  have hin (n : ℤ) : (W ((Int.divModEquiv q n).2.val : ZMod q) : ℂ) =
      (W (n : ZMod q) : ℂ) := by rw [divModEquiv_residue_cast (dvd_refl q)]
  have hp := periodic_weighted_poisson_scaled q X hX
    (fun a : Fin q => (W (a.val : ZMod q) : ℂ)) SchwartzCutoff.psi
  simp_rw [hin] at hp
  rw [hp]
  rw [tsum_eq_single 0]
  · simp only [Int.cast_zero, zero_mul, zero_div, fourier_zero, mul_one]
    have hs : (∑ a : Fin q, (W (a.val : ZMod q) : ℂ)) = (q : ℂ) := by
      rw [sum_fin_residues_eq_sum_zmod q (fun a => (W a : ℂ)), ← Complex.ofReal_sum, hW]
      norm_cast
    rw [hs]
    have hq : (q : ℂ) ≠ 0 := by exact_mod_cast (NeZero.ne q)
    push_cast
    field_simp
  · intro h hh
    rw [cutoff_nonzero_periodic_frequency hX hscale hh]
    simp

theorem amplifier_cutoff_mass {ι : Type*} [Fintype ι]
    (p : ι → ℕ) [∀ i, NeZero (p i)]
    (hcop : Pairwise (fun i j => (p i).Coprime (p j)))
    (S : ∀ i, Finset (ZMod (p i))) (lam : ℝ)
    (X : ℝ) (hX : 0 < X) (hscale : (1 : ℝ) / 4 ≤ X / (∏ i, p i : ℕ)) :
    (∑' n : ℤ, (amplifier p hcop S lam (n : ZMod (∏ i, p i)) : ℂ) *
      SchwartzCutoff.psi ((n : ℝ) / X)) = (X : ℂ) * 𝓕 SchwartzCutoff.psi 0 := by
  let : NeZero (∏ i, p i) := ⟨Finset.prod_ne_zero_iff.mpr (fun i _ => NeZero.ne (p i))⟩
  exact periodic_cutoff_mass (amplifier p hcop S lam) (sum_amplifier p hcop S lam) X hX hscale

end Ostmann.QuadraticCenter

end OAI
