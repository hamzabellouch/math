import Mathlib
import OAI.Probability.SKBarriers.Calculus.BilinearSchur

namespace OAI

section
section
noncomputable section
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
noncomputable section
open MeasureTheory Set Filter
open scoped Topology Interval
noncomputable section
open MeasureTheory Set
open scoped Interval
namespace SK.Analytic
section HessianAlgebra
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem hessian_add {f g : E → ℝ} (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g)
    (x u v : E) : Hessian (fun z => f z+g z) x u v = Hessian f x u v + Hessian g x u v := by
  have hD : fderiv ℝ (fun z => f z+g z) = fun z => fderiv ℝ f z + fderiv ℝ g z := by
    funext z
    exact fderiv_add (hf.differentiable (by norm_num) z) (hg.differentiable (by norm_num) z)
  have hdf := (hf.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  have hdg := (hg.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  have hdSum : HasFDerivAt (fun z => fderiv ℝ f z + fderiv ℝ g z)
      (fderiv ℝ (fderiv ℝ f) x + fderiv ℝ (fderiv ℝ g) x) x :=
    (hdf x).hasFDerivAt.add (hdg x).hasFDerivAt
  rw [Hessian, hD, hdSum.fderiv]
  rfl

theorem hessian_const_mul {f : E → ℝ} (hf : ContDiff ℝ 2 f) (c : ℝ)
    (x u v : E) : Hessian (fun z => c*f z) x u v = c * Hessian f x u v := by
  have hD : fderiv ℝ (fun z => c*f z) = fun z => c • fderiv ℝ f z := by
    funext z
    exact ((hf.differentiable (by norm_num) z).hasFDerivAt.const_mul c).fderiv
  have hdf := (hf.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  have hdMul : HasFDerivAt (fun z => c • fderiv ℝ f z)
      (c • fderiv ℝ (fderiv ℝ f) x) x := (hdf x).hasFDerivAt.const_smul c
  rw [Hessian, hD, hdMul.fderiv]
  rfl

theorem hessian_linear_product (a b : E →L[ℝ] ℝ) (x u v : E) :
    Hessian (fun z => a z*b z) x u v = a u*b v + b u*a v := by
  have hD : fderiv ℝ (fun z => a z*b z) = fun z => a z • b + b z • a := by
    funext z
    exact (a.hasFDerivAt.mul b.hasFDerivAt).fderiv
  have hdProd : HasFDerivAt (fun z => a z • b + b z • a)
      (a.smulRight b + b.smulRight a) x :=
    (a.hasFDerivAt.smul_const b).add (b.hasFDerivAt.smul_const a)
  rw [Hessian, hD, hdProd.fderiv]
  rfl

theorem hessian_tilt_lower {V : E → ℝ} (hV : ContDiff ℝ 2 V)
    (p L : E →L[ℝ] ℝ) (q : E → ℝ) {c ε A : ℝ}
    (hε : ε < c) (hA : 0 ≤ A) (hq : ∀ u, 0 ≤ q u)
    (hL : ∀ u, (L u)^2 ≤ A*q u)
    (hH : ∀ z u, c*q u ≤ Hessian V z u u) (z u : E) :
    ε*q u ≤ Hessian (fun z => V z - p z * L z + (A/(c-ε)/2)*(p z*p z)) z u u := by
  have hpL : ContDiff ℝ 2 (fun z => p z * L z) := p.contDiff.mul L.contDiff
  have hpp : ContDiff ℝ 2 (fun z => p z * p z) := p.contDiff.mul p.contDiff
  have heq : (fun z => V z-p z*L z+(A/(c-ε)/2)*(p z*p z)) =
      (fun z => (V z+(-1)*(p z*L z))+(A/(c-ε)/2)*(p z*p z)) := by funext z; ring
  rw [heq, hessian_add (hV.add (contDiff_const.mul hpL)) (contDiff_const.mul hpp),
    hessian_add hV (contDiff_const.mul hpL), hessian_const_mul hpL,
    hessian_const_mul hpp, hessian_linear_product, hessian_linear_product]
  have hd : 0 < c-ε := sub_pos.mpr hε
  have hbound : 2*(p u*L u) ≤ (c-ε)*q u + A/(c-ε)*(p u)^2 := by
    by_cases hAz : A = 0
    · have hLu : L u = 0 := by have := hL u; rw [hAz, zero_mul] at this; nlinarith [sq_nonneg (L u)]
      rw [hAz, zero_div, zero_mul, hLu, mul_zero, mul_zero, add_zero]
      exact mul_nonneg hd.le (hq u)
    · have hAp : 0 < A := lt_of_le_of_ne hA (Ne.symm hAz)
      have hC : 0 ≤ q u - (L u)^2/A := sub_nonneg.mpr ((div_le_iff₀ hAp).mpr (by simpa only [mul_comm] using hL u))
      have hF : 0 ≤ (c-ε)*(q u-(L u)^2/A) +
          (A*p u-(c-ε)*L u)^2/(A*(c-ε)) :=
        add_nonneg (mul_nonneg hd.le hC)
          (div_nonneg (sq_nonneg _) (mul_pos hAp hd).le)
      have he : (c-ε)*(q u-(L u)^2/A) +
          (A*p u-(c-ε)*L u)^2/(A*(c-ε)) =
          (c-ε)*q u + A/(c-ε)*(p u)^2 - 2*(p u*L u) := by
        field_simp
        ring
      linarith [he]
  have hVz := hH z u
  nlinarith
end HessianAlgebra
end SK.Analytic

end
end
end
end
end

end OAI
