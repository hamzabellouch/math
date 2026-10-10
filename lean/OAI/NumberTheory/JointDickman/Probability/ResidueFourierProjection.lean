import OAI.NumberTheory.JointDickman.Arithmetic.RamanujanDivisorFormula

namespace OAI

/-! # The finite residue-average projection is an L2 contraction -/

namespace JointDickman
open Finset

noncomputable def complexResidueMean {q : ℕ} [NeZero q] (v : (ZMod q)ˣ → ℂ) : ℂ :=
  (∑ r, v r)/(q.totient : ℂ)

theorem complexResidueMean_square_le {q : ℕ} [NeZero q] (v : (ZMod q)ˣ → ℂ) :
    (q.totient : ℝ)*‖complexResidueMean v‖^2 ≤ ∑ r, ‖v r‖^2 := by
  have hφ : (0 : ℝ) < q.totient := by exact_mod_cast Nat.totient_pos.mpr (NeZero.pos q)
  have hn := norm_sum_le univ v
  have hsq : ‖∑ r, v r‖^2 ≤ (∑ r, ‖v r‖)^2 :=
    (sq_le_sq₀ (norm_nonneg _) (sum_nonneg (fun r _ => norm_nonneg _))).mpr hn
  have hcs := sum_mul_sq_le_sq_mul_sq univ (fun _ : (ZMod q)ˣ => (1 : ℝ)) (fun r => ‖v r‖)
  simp only [one_mul,one_pow,sum_const,card_univ,nsmul_eq_mul,mul_one,ZMod.card_units_eq_totient] at hcs
  have hh := hsq.trans hcs
  rw [complexResidueMean,norm_div,Complex.norm_natCast,div_pow]
  have he : (q.totient : ℝ)*(‖∑ r, v r‖^2/(q.totient : ℝ)^2) =
      ‖∑ r, v r‖^2/(q.totient : ℝ) := by field_simp
  rw [he]
  exact (div_le_iff₀ hφ).mpr (by simpa only [mul_comm] using hh)

theorem unitResidueFourier_projection_contract {q : ℕ} [NeZero q]
    (v : (ZMod q)ˣ → ℂ) :
    (∑ h : ZMod q, ‖unitResidueFourier (fun _ => complexResidueMean v) h‖^2) ≤
      ∑ h : ZMod q, ‖unitResidueFourier v h‖^2 := by
  rw [unitResidue_fourier_parseval,unitResidue_fourier_parseval]
  simp only [sum_const,card_univ,nsmul_eq_mul,ZMod.card_units_eq_totient]
  exact mul_le_mul_of_nonneg_left (complexResidueMean_square_le v) (Nat.cast_nonneg q)

theorem unitResidueFourier_projected {q : ℕ} [NeZero q]
    (v : (ZMod q)ˣ → ℂ) (h : ZMod q) :
    unitResidueFourier (fun _ => complexResidueMean v) h =
      (ramanujanSum q h/(q.totient : ℂ))*(∑ r, v r) := by
  unfold unitResidueFourier complexResidueMean ramanujanSum
  rw [← sum_mul]
  ring

theorem unitResidueFourier_centered {q : ℕ} [NeZero q]
    (v : (ZMod q)ˣ → ℂ) (h : ZMod q) :
    unitResidueFourier v h-unitResidueFourier (fun _ => complexResidueMean v) h =
      unitResidueFourier (fun r => v r-complexResidueMean v) h := by
  simp only [unitResidueFourier,mul_sub,sum_sub_distrib]

end JointDickman

end OAI
