import Mathlib

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

theorem bilinear_schur_lower
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (H : (E × ℝ) →L[ℝ] (E × ℝ) →L[ℝ] ℝ)
    (hH : ∀ u v, H u v = H v u)
    (q : E → ℝ) (hq : q 0 = 0) {c : ℝ} (hc : 0 < c)
    (hlower : ∀ u s, c * (q u + s^2) ≤ H (u,s) (u,s)) (u : E) :
    0 < H (0,1) (0,1) ∧
    c * q u ≤ H (u,0) (u,0) - H (0,1) (u,0)^2 / H (0,1) (0,1) := by
  have hD : c ≤ H (0,1) (0,1) := by simpa [hq] using hlower 0 1
  have hD₀ := hc.trans_le hD
  refine ⟨hD₀, ?_⟩
  let A := H (u,0) (u,0)
  let B := H (0,1) (u,0)
  let D := H (0,1) (0,1)
  have heq (s : ℝ) : H (u,s) (u,s) = A + 2*s*B + s^2*D := by
    have hvec : (u,s) = (u,0) + s • (0,1) := by simp
    rw [hvec]
    simp only [map_add, map_smul, add_apply,
      smul_apply, smul_eq_mul]
    rw [hH (u,0) (0,1)]
    dsimp [A,B,D]
    ring
  have h := hlower u (-B/D)
  rw [heq] at h
  have hR : A + 2*(-B/D)*B + (-B/D)^2*D = A-B^2/D := by
    field_simp
    ring
  rw [hR] at h
  have hh : 0 ≤ c * (-B/D)^2 := mul_nonneg hc.le (sq_nonneg _)
  change c*q u ≤ A-B^2/D
  nlinarith

def Hessian {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (V : E → ℝ) (x u v : E) : ℝ := fderiv ℝ (fderiv ℝ V) x u v

theorem hasDerivAt_affine_comp
    {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : E → F) (hf : Differentiable ℝ f) (x u : E) (t : ℝ) :
    HasDerivAt (fun s => f (x+s • u)) (fderiv ℝ f (x+t • u) u) t := by
  have h := (hf (x+t • u)).hasFDerivAt.comp_hasDerivAt t
    ((hasDerivAt_id t).smul_const u |>.const_add x)
  simpa only [Function.comp_def, one_smul, id_eq] using h

theorem hasDerivAt_affine_score
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (V : E → ℝ) (hV : ContDiff ℝ 2 V) (x u v : E) (t : ℝ) :
    HasDerivAt (fun s => fderiv ℝ V (x+s • u) v) (Hessian V (x+t • u) u v) t := by
  have hd : Differentiable ℝ (fderiv ℝ V) :=
    (hV.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  have h := hasDerivAt_affine_comp (fderiv ℝ V) hd x u t
  simpa only [map_zero, add_zero, Hessian] using h.clm_apply (hasDerivAt_const t v)

end SK.Analytic

end
end
end
end
end

end OAI
