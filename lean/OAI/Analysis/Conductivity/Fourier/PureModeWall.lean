import Mathlib
import OAI.Analysis.Conductivity.Walls.RecenteredWallField

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Real Set Filter Topology

def pureWallMode (σ lam k : ℝ) (x : Box3) : ℝ :=
  σ*exp (-lam*x.1.1)*cos (k*x.2)

lemma pureWallMode_smooth (σ lam k : ℝ) :
    ContDiff ℝ (↑(⊤:ℕ∞)) (pureWallMode σ lam k) := by
  unfold pureWallMode
  fun_prop

lemma pureWallMode_normalDerivative (σ lam k : ℝ) (q : ℝ×ℝ) (z : ℝ) :
    wallDerivative (pureWallMode σ lam k) (q,z)=
      σ*exp (-lam*q.1)*(-sin (k*z)*k) := by
  apply wallDerivative_eq_of_hasDeriv ((pureWallMode_smooth σ lam k).differentiable (by simp))
  simpa only [pureWallMode,mul_one,id_eq] using
    (((hasDerivAt_id z).const_mul k).cos.const_mul (σ*exp (-lam*q.1)))

lemma pureWallMode_normalSecond (σ lam k : ℝ) (q : ℝ×ℝ) (z : ℝ) :
    wallDerivative (wallDerivative (pureWallMode σ lam k)) (q,z)=
      -(σ*exp (-lam*q.1)*cos (k*z)*k^2) := by
  apply wallDerivative_eq_of_hasDeriv
    ((wallDerivative_smooth (pureWallMode_smooth σ lam k)).differentiable (by simp))
  have h := (((((hasDerivAt_id z).const_mul k).sin.neg).mul_const k).const_mul
    (σ*exp (-lam*q.1)))
  convert! h using 1 <;> first | rfl | (simp only [pureWallMode_normalDerivative,id_eq,Pi.neg_apply] <;> ring)

lemma pureWallMode_wall_value (σ lam k : ℝ) (q : ℝ×ℝ) :
    pureWallMode σ lam k (q,0)=σ*exp (-lam*q.1) := by simp [pureWallMode]

lemma pureWallMode_wall_critical (σ lam k : ℝ) (q : ℝ×ℝ) :
    wallDerivative (pureWallMode σ lam k) (q,0)=0 := by
  simp [pureWallMode_normalDerivative]

lemma pureWallMode_wall_simple {σ lam k : ℝ} (hσ : σ≠0) (hk : k≠0) (q : ℝ×ℝ) :
    wallDerivative (wallDerivative (pureWallMode σ lam k)) (q,0)≠0 := by
  rw [pureWallMode_normalSecond]
  simp only [mul_zero,cos_zero,mul_one,neg_ne_zero]
  exact mul_ne_zero (mul_ne_zero hσ (exp_ne_zero _)) (pow_ne_zero 2 hk)

lemma sin_ne_zero_of_abs_lt_pi {z : ℝ} (hz : z≠0) (hp : |z|<Real.pi) : sin z≠0 := by
  rcases lt_or_gt_of_ne hz with hn | hpz
  · have h := (sin_pos_of_pos_of_lt_pi (neg_pos.mpr hn) (by linarith [(abs_lt.mp hp).1])).ne'
    simpa only [sin_neg,neg_ne_zero] using h
  · exact (sin_pos_of_pos_of_lt_pi hpz (abs_lt.mp hp).2).ne'

lemma pureWallMode_quotient_nonzero {σ lam k : ℝ} (hσ : σ≠0) (hk : k≠0)
    (q : ℝ×ℝ) {z : ℝ} (hz : |k*z|<Real.pi) :
    wallQuotient (wallDerivative (pureWallMode σ lam k)) (q,z)≠0 := by
  by_cases h0 : z=0
  · subst z
    rw [wallQuotient_zero]
    exact pureWallMode_wall_simple hσ hk q
  have hd : wallDerivative (pureWallMode σ lam k) (q,z)≠0 := by
    rw [pureWallMode_normalDerivative]
    exact mul_ne_zero (mul_ne_zero hσ (exp_ne_zero _))
      (mul_ne_zero (neg_ne_zero.mpr (sin_ne_zero_of_abs_lt_pi (mul_ne_zero hk h0) hz)) hk)
  have he := (smooth_wall_division (wallDerivative_smooth (pureWallMode_smooth σ lam k))
    (pureWallMode_wall_critical σ lam k)).2 (q,z)
  exact (mul_ne_zero_iff.mp (he ▸ hd)).2

end ScalarConductivity

end
end

end OAI
