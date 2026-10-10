import OAI.NumberTheory.Ostmann.Supply.UniformDecomposition

namespace OAI

noncomputable section
namespace Ostmann.Supply
open scoped BigOperators ComplexConjugate
variable {p : ℕ} [NeZero p]

theorem uniformVector_norm_sq (S : Finset (ZMod p)) (hS : S.Nonempty) :
    ‖uniformVector S‖^2 = (S.card:ℝ)⁻¹ := by
  have hs : (S.card:ℝ) ≠ 0 := by exact_mod_cast Finset.card_ne_zero.mpr hS
  rw [PiLp.norm_sq_eq_of_L2]
  simp only [uniformVector_apply, apply_ite, norm_zero, ite_pow,
    zero_pow (by decide : 2 ≠ 0), norm_inv, Complex.norm_natCast,
    Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul]
  field_simp

theorem uniformCoefficient_nonneg (S : Finset (ZMod p)) :
    0 ≤ uniformCoefficient S := div_nonneg (Real.sqrt_nonneg _) (Nat.cast_nonneg _)

theorem density_compl (S : Finset (ZMod p)) : density Sᶜ = 1-density S := by
  have hc := Finset.card_add_card_compl S
  rw [ZMod.card p] at hc
  have hp : (p:ℝ) ≠ 0 := by exact_mod_cast NeZero.ne p
  have hcr : (S.card:ℝ)+(Sᶜ.card:ℝ) = p := by exact_mod_cast hc
  simp only [density,ZMod.card]
  field_simp
  linarith

theorem uniformCoefficient_mul_compl (S : Finset (ZMod p))
    (hpos : 0 < density S) (hlt : density S < 1) :
    uniformCoefficient S * uniformCoefficient Sᶜ = (p:ℝ)⁻¹^2 := by
  have hp : (p:ℝ) ≠ 0 := by exact_mod_cast NeZero.ne p
  have hs : (S.card:ℝ) ≠ 0 := by
    intro hh
    simp [density,hh] at hpos
  have ht : (Sᶜ.card:ℝ) ≠ 0 := by
    intro hh
    have hd := density_compl S
    simp [density,hh] at hd
    simp only [density,ZMod.card] at hlt
    linarith
  have hv : 0 ≤ density S*(1-density S) := by positivity
  have he : (1-density S)*(1-(1-density S)) = density S*(1-density S) := by ring
  simp only [uniformCoefficient,density_compl,he]
  rw [div_mul_div_comm, ← pow_two,Real.sq_sqrt hv]
  have hc := Finset.card_add_card_compl S
  rw [ZMod.card p] at hc
  have hcr : (S.card:ℝ)+(Sᶜ.card:ℝ) = p := by exact_mod_cast hc
  simp only [density,ZMod.card]
  field_simp
  nlinarith

theorem uniformCoefficient_le (S : Finset (ZMod p))
    (hlo : (1/3:ℝ) ≤ density S) (hhi : density S ≤ 2/3) :
    uniformCoefficient S ≤ 2/(p:ℝ) := by
  have hp : (0:ℝ) < p := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne p))
  have hs : (0:ℝ) < S.card := by
    have hh : 0 < density S := by linarith
    exact (div_pos_iff_of_pos_right hp).mp (by simpa [density,ZMod.card] using hh)
  have hvar : 0 ≤ density S*(1-density S) :=
    mul_nonneg (by linarith) (by linarith)
  have hroot : Real.sqrt (density S*(1-density S)) ≤ 2*density S := by
    have hsq := Real.sq_sqrt hvar
    have hd0 : 0 ≤ density S := by linarith
    nlinarith [mul_nonneg hd0 (by linarith : 0 ≤ 5*density S-1), Real.sqrt_nonneg (density S*(1-density S))]
  have hh := (div_le_div_of_nonneg_right hroot hs.le)
  have he : (2*density S)/(S.card:ℝ) = 2/(p:ℝ) := by
    simp only [density,ZMod.card]
    field_simp
  simpa only [uniformCoefficient,he] using hh

end Ostmann.Supply

end

end OAI
