import Mathlib
import OAI.Analysis.AffineBernstein.WeightedTracefreeMatrix
import OAI.Analysis.AffineBernstein.ConstantDetCalculus

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein
noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal

section DirectionalJacobi
open Matrix

lemma constant_det_directional_jacobi {n : ℕ} (hn : 1 ≤ n) {u : Space n → ℝ}
    (hu : ContDiff ℝ ∞ u) (hp : ∀ x, (hessian u x).PosDef)
    (hD : ∀ x y, (hessian u x).det=(hessian u y).det) (e x : Space n) :
    ((n:ℝ)+1)*inverseHessianPair u (dirDeriv e (dirDeriv e u)) (dirDeriv e (dirDeriv e u)) x ≤
      (n:ℝ)*dirDeriv e (dirDeriv e u) x*inverseHessianTrace u (dirDeriv e (dirDeriv e u)) x := by
  let B := hessian (dirDeriv e u) x
  let A := hessian u x
  have hB : B.IsSymm := hessian_isSymm (contDiff_dirDeriv hu e).contDiffAt
  have hq : inverseHessianPair u (dirDeriv e (dirDeriv e u)) (dirDeriv e (dirDeriv e u)) x =
      (fun i => e i) ⬝ᵥ ((B*A⁻¹*B)*ᵥ (fun i => e i)) := by
    rw [Matrix.mul_assoc,← Matrix.mulVec_mulVec,← Matrix.mulVec_mulVec,Matrix.dotProduct_mulVec,
      ← Matrix.mulVec_transpose,show B.transpose=B from hB]
    simp only [inverseHessianPair,directional_second_gradient hu,Matrix.mulVec,dotProduct,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro coordinate _
    apply Finset.sum_congr rfl
    intro otherCoordinate _
    dsimp only [B,A]
    simp only [← Finset.mul_sum]
    ring
  have hf : dirDeriv e (dirDeriv e u) x = (fun i => e i) ⬝ᵥ (A*ᵥ (fun i => e i)) := by
    rw [dirDeriv_eq_second hu.contDiffAt,second_fderiv_eq_sum hu.contDiffAt]
    simp only [A,dotProduct,Matrix.mulVec,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro coordinate _
    apply Finset.sum_congr rfl
    intro otherCoordinate _
    ring
  rw [hq,hf,constant_det_directional_equation hu hp hD]
  exact weighted_tracefree_quadratic_gap hn (hp x) (Matrix.isHermitian_iff_isSymm.mpr hB)
    (constant_det_trace_diff_zero hu hp hD e x) (fun i => e i)

lemma inverseHessianTrace_expMul {n : ℕ} {u f : Space n → ℝ}
    (hf : ContDiff ℝ ∞ f) (c : ℝ) (x : Space n) :
    inverseHessianTrace u (fun y => Real.exp (c*f y)) x =
      Real.exp (c*f x)*(c*inverseHessianTrace u f x+c^2*inverseHessianPair u f f x) := by
  have he (i j : Fin n) : hessian (fun y => Real.exp (c*f y)) x i j =
      Real.exp (c*f x)*(c*hessian f x i j+c^2*dirDeriv (coordinateVector n i) f x*dirDeriv (coordinateVector n j) f x) :=
    second_dirDeriv_expMul isOpen_univ hf.contDiffOn (mem_univ x) c _ _
  simp only [inverseHessianTrace,inverseHessianPair,he,mul_add,Finset.sum_add_distrib,Finset.mul_sum]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro coordinate _ <;>
    apply Finset.sum_congr rfl <;> intro otherCoordinate _ <;> ring

lemma inverseHessianPair_log_positive {n : ℕ} {u f : Space n → ℝ}
    (hf : ContDiff ℝ ∞ f) (hpos : ∀ x, 0 < f x) (x : Space n) :
    inverseHessianPair u (fun y => Real.log (f y)) (fun y => Real.log (f y)) x =
      inverseHessianPair u f f x/(f x)^2 := by
  simp only [inverseHessianPair,dirDeriv_real_log (hf.differentiable (by simp) x) (hpos x).ne',
    Finset.sum_div]
  apply Finset.sum_congr rfl
  intro coordinate _
  apply Finset.sum_congr rfl
  intro otherCoordinate _
  ring

lemma inverseHessianTrace_log_positive {n : ℕ} {u f : Space n → ℝ}
    (hf : ContDiff ℝ ∞ f) (hpos : ∀ x, 0 < f x) (x : Space n) :
    inverseHessianTrace u (fun y => Real.log (f y)) x =
      inverseHessianTrace u f x/f x-inverseHessianPair u f f x/(f x)^2 := by
  have he : inverseHessianTrace u f x = f x *
      (inverseHessianTrace u (fun y => Real.log (f y)) x +
        inverseHessianPair u (fun y => Real.log (f y)) (fun y => Real.log (f y)) x) := by
    simp only [inverseHessianTrace,inverseHessianPair,mul_add,Finset.mul_sum]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    have hh := log_second_identity isOpen_univ hf.contDiffOn (fun y _ => hpos y)
      (mem_univ x) (coordinateVector n i) (coordinateVector n j)
    change hessian f x i j = f x * (hessian (fun y => Real.log (f y)) x i j + _) at hh
    rw [hh]
    ring
  rw [inverseHessianPair_log_positive hf hpos] at he
  apply eq_sub_iff_add_eq.mpr
  apply (eq_div_iff (hpos x).ne').mpr
  simpa only [mul_comm] using he.symm

/-- A convenient exact representation of the reciprocal n-th root, always
used on a strictly positive directional Hessian. -/
def inverseNthRoot (n : ℕ) (f : Space n → ℝ) (x : Space n) : ℝ :=
  Real.exp (-((n:ℝ)⁻¹)*Real.log (f x))

lemma inverseNthRoot_pos {n : ℕ} (f : Space n → ℝ) (x : Space n) : 0 < inverseNthRoot n f x :=
  Real.exp_pos _

lemma contDiff_inverseNthRoot {n : ℕ} {f : Space n → ℝ} (hf : ContDiff ℝ ∞ f)
    (hpos : ∀ x, 0 < f x) : ContDiff ℝ ∞ (inverseNthRoot n f) :=
  (contDiff_const.mul (hf.log (fun x => (hpos x).ne'))).exp

lemma inverseNthRoot_pow {n : ℕ} (hn : 1 ≤ n) {f : Space n → ℝ}
    {x : Space n} (hf : 0 < f x) : (inverseNthRoot n f x)^n = (f x)⁻¹ := by
  have hn0 : (n:ℝ) ≠ 0 := by exact_mod_cast (by omega : n≠0)
  rw [inverseNthRoot,← Real.exp_nat_mul]
  have he : (n:ℝ)*(-((n:ℝ)⁻¹)*Real.log (f x)) = -Real.log (f x) := by field_simp
  rw [he,Real.exp_neg,Real.exp_log hf]

lemma inverseNthRoot_supersolution_of_jacobi {n : ℕ} (hn : 1 ≤ n) {u f : Space n → ℝ}
    (hf : ContDiff ℝ ∞ f) (hpos : ∀ x, 0 < f x)
    (hJ : ∀ x, ((n:ℝ)+1)*inverseHessianPair u f f x ≤ (n:ℝ)*f x*inverseHessianTrace u f x) :
    ∀ x, inverseHessianTrace u (inverseNthRoot n f) x ≤ 0 := by
  intro x
  have hn0 : 0 < (n:ℝ) := by exact_mod_cast (Nat.succ_le_iff.mp hn)
  have hlog : ContDiff ℝ ∞ (fun y => Real.log (f y)) := hf.log (fun y => (hpos y).ne')
  change inverseHessianTrace u (fun y => Real.exp (-((n:ℝ)⁻¹)*Real.log (f y))) x ≤ 0
  rw [inverseHessianTrace_expMul hlog,inverseHessianTrace_log_positive hf hpos,
    inverseHessianPair_log_positive hf hpos]
  apply mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le
  have H := hJ x
  have hfx := hpos x
  apply (mul_le_mul_iff_right₀ (show 0 < (n:ℝ)^2*(f x)^2 by positivity)).mp
  rw [mul_zero]
  field_simp [hn0.ne',(hpos x).ne']
  nlinarith

lemma constant_det_directional_inverse_root_supersolution {n : ℕ} (hn : 1 ≤ n) {u : Space n → ℝ}
    (hu : ContDiff ℝ ∞ u) (hp : ∀ x, (hessian u x).PosDef)
    (hD : ∀ x y, (hessian u x).det=(hessian u y).det) {e : Space n} (he : e ≠ 0) :
    ∀ x, inverseHessianTrace u (inverseNthRoot n (dirDeriv e (dirDeriv e u))) x ≤ 0 := by
  apply inverseNthRoot_supersolution_of_jacobi hn (contDiff_dirDeriv (contDiff_dirDeriv hu e) e)
  · intro x
    rw [dirDeriv_eq_second hu.contDiffAt]
    exact second_fderiv_pos hu.contDiffAt (hp x) he
  · exact fun x => constant_det_directional_jacobi hn hu hp hD e x

end DirectionalJacobi


end
end AffineBernstein
end

end OAI
