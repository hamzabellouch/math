import Mathlib

namespace OAI

open Matrix

namespace CurrentKS.Scalar
noncomputable section
open scoped ContDiff

def psi (x : ℝ) : ℝ := (1-x^2) ^ (1/3 : ℝ)
def psi₁ (x : ℝ) : ℝ := -2*x / (3*psi x^2)
def kappa (x : ℝ) : ℝ := 2*(3+x^2) / (9*psi x^5)

lemma base_pos {x : ℝ} (hx : |x| < 1) : 0 < 1-x^2 := by
  have h := (abs_lt.mp hx)
  nlinarith [sq_nonneg x]

lemma psi_pos {x : ℝ} (hx : |x| < 1) : 0 < psi x :=
  Real.rpow_pos_of_pos (base_pos hx) _

lemma psi_cube {x : ℝ} (hx : |x| < 1) : psi x ^ 3 = 1-x^2 := by
  rw [psi, ← Real.rpow_natCast, ← Real.rpow_mul (le_of_lt (base_pos hx))]
  norm_num

lemma psi_sq {x : ℝ} (hx : |x| < 1) : psi x ^ 2 = (1-x^2) ^ (2/3 : ℝ) := by
  rw [psi, ← Real.rpow_natCast, ← Real.rpow_mul (le_of_lt (base_pos hx))]
  norm_num

lemma psi_le_one {x : ℝ} (hx : |x| < 1) : psi x ≤ 1 := by
  have hp := psi_pos hx
  have hc := psi_cube hx
  nlinarith [sq_nonneg x, sq_nonneg (psi x - 1)]

lemma hasDerivAt_psi {x : ℝ} (hx : |x| < 1) : HasDerivAt psi (psi₁ x) x := by
  have hr := ((hasDerivAt_const x (1 : ℝ)).sub ((hasDerivAt_id x).pow 2)).rpow_const
    (p := (1/3 : ℝ)) (Or.inl (ne_of_gt (base_pos hx)))
  convert hr using 1 <;> try rfl
  norm_num only [mul_one, zero_sub, Nat.cast_ofNat]
  simp only [id_eq, pow_one, Pi.sub_apply, Pi.pow_apply]
  rw [Real.rpow_neg (base_pos hx).le, ← psi_sq hx]
  unfold psi₁
  ring

lemma contDiffAt_psi {x : ℝ} (hx : |x| < 1) {n : WithTop ℕ∞} : ContDiffAt ℝ n psi x := by
  exact (Real.contDiffAt_rpow_const_of_ne (ne_of_gt (base_pos hx))).comp x
    (contDiffAt_const.sub (contDiffAt_id.pow 2))

lemma hasDerivAt_psi₁ {x : ℝ} (hx : |x| < 1) : HasDerivAt psi₁ (-kappa x) x := by
  have hw : psi x ≠ 0 := ne_of_gt (psi_pos hx)
  have hp := hasDerivAt_psi hx
  have hd := ((hasDerivAt_id x).const_mul (-2)).div ((hp.pow 2).const_mul 3)
    (by positivity : (3 : ℝ) * psi x^2 ≠ 0)
  convert hd using 1 <;> try rfl
  simp only [Pi.pow_apply, id_eq, Nat.cast_ofNat, Nat.reduceSub, pow_one, mul_one]
  unfold kappa psi₁
  have hc := psi_cube hx
  field_simp
  nlinarith [hc]

lemma kappa_pos {x : ℝ} (hx : |x| < 1) : 0 < kappa x := by
  unfold kappa
  have h := psi_pos hx
  positivity

lemma derivative_ratio {x : ℝ} (hx : |x| < 1) :
    psi₁ x ^ 2 / (psi x * kappa x) = 2*x^2/(3+x^2) := by
  have hw := ne_of_gt (psi_pos hx)
  have hx3 : 3+x^2 ≠ 0 := by positivity
  unfold psi₁ kappa
  field_simp
  ring

lemma derivative_ratio_le {x : ℝ} (hx : |x| < 1) :
    psi₁ x ^ 2 / (psi x * kappa x) ≤ (1/2 : ℝ) := by
  rw [derivative_ratio hx]
  have hp : 0 < 3+x^2 := by positivity
  apply (div_le_iff₀ hp).mpr
  have hb := base_pos hx
  nlinarith

lemma psi₁_eq_base {x : ℝ} (hx : |x| < 1) :
    psi₁ x = -(2*x/(3*(1-x^2))) * psi x := by
  have hw := ne_of_gt (psi_pos hx)
  have hb := ne_of_gt (base_pos hx)
  unfold psi₁
  field_simp
  have hc := psi_cube hx
  rw [hc]

end
end CurrentKS.Scalar

end OAI
