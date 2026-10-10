import OAI.NumberTheory.DirichletL.Hecke.PrimeDyadicBuffered
import OAI.NumberTheory.DirichletL.Hecke.DyadicScale

namespace OAI

noncomputable section
namespace SevenEighths.HeckePrimeDyadic
open HeckeFamily HeckeDyadic HeckeDeletionBounds HeckeLogarithmic

theorem binCost_le_log (χ : Character) (B U H η : ℝ)
    (hB : 0≤B) (hU : 2≤U) (hQ : (χ.modulus.absNorm : ℝ)≤U)
    (hheight : (3+|H|)^2≤U^η) :
    binCost B χ H ≤ (B*(2+η)+localBound (1/2))*Real.log U := by
  have hUp : 0<U := by linarith
  have hcp : 0<complexity χ H := (Real.exp_pos 1).trans_le (complexity_ge_exp χ H)
  have hcomplex : complexity χ H ≤ 2*U^(1+η) := by
    unfold complexity
    calc
      2*(χ.modulus.absNorm : ℝ)*(3+|H|)^2 ≤ 2*U*U^η := by gcongr
      _ = _ := by rw [Real.rpow_add hUp, Real.rpow_one]; ring
  have hlog : Real.log (complexity χ H) ≤ (2+η)*Real.log U := by
    apply (Real.log_le_log hcp hcomplex).trans
    rw [Real.log_mul (by norm_num) (Real.rpow_pos_of_pos hUp _).ne', Real.log_rpow hUp]
    have h2 := Real.log_le_log (by norm_num : (0 : ℝ)<2) hU
    nlinarith
  have hrad : 0<((radical χ.modulus).absNorm : ℝ) := by
    exact_mod_cast Nat.pos_iff_ne_zero.mpr
      (Ideal.absNorm_eq_zero_iff.not.mpr (radical_ne_zero χ.modulus))
  have hrlog := Real.log_le_log hrad ((radical_norm_le_modulus χ).trans hQ)
  unfold binCost
  calc
    _ ≤ B*((2+η)*Real.log U)+localBound (1/2)*Real.log U :=
      add_le_add (mul_le_mul_of_nonneg_left hlog hB)
        (mul_le_mul_of_nonneg_left hrlog (localBound_pos (by norm_num : (0 : ℝ)<1/2)).le)
    _ = _ := by ring

theorem binCost_le_power (χ : Character) (B U H η ε : ℝ)
    (hB : 0≤B) (hU : 2≤U) (hQ : (χ.modulus.absNorm : ℝ)≤U)
    (hη : 0≤η) (hε : 0<ε) (hheight : (3+|H|)^2≤U^η) :
    binCost B χ H ≤ ((B*(2+η)+localBound (1/2))/ε)*U^ε := by
  apply (binCost_le_log χ B U H η hB hU hQ hheight).trans
  have hc : 0≤B*(2+η)+localBound (1/2) := by
    exact add_nonneg (mul_nonneg hB (by linarith))
      (localBound_pos (by norm_num : (0 : ℝ)<1/2)).le
  have hh := mul_le_mul_of_nonneg_left
    (Real.log_le_rpow_div (by linarith : 0≤U) hε) hc
  convert hh using 1 ; ring

end SevenEighths.HeckePrimeDyadic

end

end OAI
