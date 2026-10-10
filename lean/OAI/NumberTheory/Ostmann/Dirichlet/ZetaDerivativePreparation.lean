import OAI.NumberTheory.Ostmann.Dirichlet.ZetaDisk

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

namespace Ostmann.Dirichlet

lemma log_zeta_envelope_bound {K : ℝ} (hK : 1 ≤ K) (t : ℝ) :
    Real.log (K * (|t| + 6) ^ 2) ≤ (Real.log K + 2) * Real.log (|t| + 6) := by
  have ht : 0 < |t| + 6 := by positivity
  have hl : 1 ≤ Real.log (|t| + 6) :=
    ((Real.lt_log_iff_exp_lt ht).mpr
      (Real.exp_one_lt_three.trans (by have := abs_nonneg t; linarith))).le
  have hlogK := Real.log_nonneg hK
  rw [Real.log_mul (by linarith) (by positivity), Real.log_pow]
  norm_num only [Nat.cast_ofNat]
  nlinarith [mul_le_mul_of_nonneg_left hl hlogK]

lemma zeta_envelope_gt_one {K : ℝ} (hK : 1 ≤ K) (t : ℝ) :
    1 < K * (|t| + 6) ^ 2 := by
  have ht := abs_nonneg t
  have hs : 1 < (|t| + 6) ^ 2 := by nlinarith
  exact hs.trans_le (le_mul_of_one_le_left (by positivity) hK)

@[simp] lemma zetaDiskPoint_ofReal (sigma t : ℝ) :
    zetaDiskPoint t ((4 / 5 * (sigma - 2) : ℝ) : ℂ) =
      (sigma : ℂ) + (t : ℂ) * Complex.I := by
  unfold zetaDiskPoint zetaCenter
  push_cast
  ring

lemma normalizedZeta_log_derivative (t : ℝ) (w : ℂ)
    (hw : regularZeta (zetaDiskPoint t w) ≠ 0) :
    deriv (normalizedZeta t) w / normalizedZeta t w =
      (5 / 4 : ℂ) * (deriv regularZeta (zetaDiskPoint t w) /
        regularZeta (zetaDiskPoint t w)) := by
  have hn := regularZeta_ne_zero_of_one_le_re (s := zetaCenter t) (by simp)
  have hp : HasDerivAt (zetaDiskPoint t) (5 / 4 : ℂ) w := by
    simpa only [zetaDiskPoint, id_eq, mul_one] using!
      (((hasDerivAt_id w).const_mul (5 / 4 : ℂ)).const_add (zetaCenter t))
  have hf : Differentiable ℂ regularZeta :=
    DirichletCharacter.differentiable_LFunctionTrivChar₁ 1
  have hd := ((hf.differentiableAt.hasDerivAt.comp w hp).div_const (regularZeta (zetaCenter t)))
  change HasDerivAt (normalizedZeta t)
    ((deriv regularZeta (zetaDiskPoint t w) * (5 / 4 : ℂ)) /
      regularZeta (zetaCenter t)) w at hd
  rw [hd.deriv]
  unfold normalizedZeta
  field_simp

end Ostmann.Dirichlet

end OAI
