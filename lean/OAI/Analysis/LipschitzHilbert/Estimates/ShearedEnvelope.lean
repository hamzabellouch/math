import OAI.Analysis.LipschitzHilbert.Estimates.PolynomialEnvelope

namespace OAI

/-! Transfer a packet's decay to a nearby reference slope. A bounded
normalized shear costs a fixed packet order and a fixed constant. -/

noncomputable section
namespace LipschitzHilbert

theorem unit_shear_envelope (x y beta : ℝ) (n : ℕ) (hbeta : |beta| ≤ 1) :
    lineEnvelope 0 1 (2*n) x*lineEnvelope 0 1 (2*n) (y-beta*x) ≤
      2^n*(lineEnvelope 0 1 n x*lineEnvelope 0 1 n y) := by
  let A := 1+x^2
  let B := 1+(y-beta*x)^2
  let C := 1+y^2
  have hA : 1 ≤ A := by dsimp [A]; nlinarith [sq_nonneg x]
  have hB : 1 ≤ B := by dsimp [B]; nlinarith [sq_nonneg (y-beta*x)]
  have hC : 1 ≤ C := by dsimp [C]; nlinarith [sq_nonneg y]
  have hb : beta^2 ≤ 1 := by nlinarith [abs_le.mp hbeta, sq_abs beta]
  have hbx : (beta*x)^2 ≤ x^2 := by nlinarith [sq_nonneg x]
  have hbase : C ≤ 2*A*B := by
    dsimp [A,B,C]
    nlinarith [sq_nonneg (y-2*(beta*x)), sq_nonneg x, sq_nonneg (y-beta*x),
      mul_nonneg (sq_nonneg x) (sq_nonneg (y-beta*x))]
  have hbig : A*C ≤ 2*(A*B)^2 := by
    have h1 := mul_le_mul_of_nonneg_left hbase (by positivity : 0 ≤ A)
    have h2 : B ≤ B^2 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left h2 (by positivity : 0 ≤ 2*A^2)]
  have hpow := pow_le_pow_left₀ (by positivity : 0 ≤ A*C) hbig n
  simp only [lineEnvelope, sub_zero, div_one]
  change (A^(2*n))⁻¹*(B^(2*n))⁻¹ ≤ 2^n*((A^n)⁻¹*(C^n)⁻¹)
  have hleft : 0 < A^(2*n)*B^(2*n) := by positivity
  have hright : 0 < A^n*C^n := by positivity
  rw [← mul_inv, ← mul_inv]
  rw [← one_div, ← div_eq_mul_inv]
  apply (div_le_div_iff₀ hleft hright).mpr
  simp only [one_mul]
  simpa only [mul_pow, ← pow_mul, Nat.mul_comm] using hpow

theorem reference_shear_envelope (x y cx cy l W s t : ℝ) (n : ℕ)
    (hl : 0 < l) (hW : 0 < W) (hclose : |(s-t)*l/W| ≤ 1) :
    lineEnvelope cx l (2*n) x*lineEnvelope (cy+s*(x-cx)) W (2*n) y ≤
      2^n*(lineEnvelope cx l n x*lineEnvelope (cy+t*(x-cx)) W n y) := by
  have heq : (y-(cy+s*(x-cx)))/W =
      (y-(cy+t*(x-cx)))/W-((s-t)*l/W)*((x-cx)/l) := by
    field_simp
    ring
  have h := unit_shear_envelope ((x-cx)/l) ((y-(cy+t*(x-cx)))/W)
    ((s-t)*l/W) n hclose
  simpa only [lineEnvelope, sub_zero, div_one, ← heq] using h

end LipschitzHilbert

end

end OAI
