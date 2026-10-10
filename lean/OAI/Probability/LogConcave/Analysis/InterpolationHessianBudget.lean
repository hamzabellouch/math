import Mathlib
import OAI.Probability.LogConcave.JetEstimates.TensorTerm
import OAI.Probability.LogConcave.JetEstimates.JetMaterial
import OAI.Probability.LogConcave.JetEstimates.Slice
import OAI.Probability.LogConcave.Sampling.MatrixColor

namespace OAI

section
section
noncomputable section
namespace LogConcaveSampling
open MeasureTheory
open scoped Classical BigOperators NNReal ENNReal RealInnerProductSpace

def interpolationHessianBudget : ℝ≥0 := ⟨1+Real.pi^2/4,by positivity⟩

lemma interpolationPotential_gradient_uniform {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r ρ : ℝ} (hr : 0≤r)
    (hl : (lam:ℝ)*r^2≤1/2) (h0 : 0≤ρ) (h1 : ρ<1) :
    LipschitzWith interpolationHessianBudget (gradient (interpolationPotential F x r ρ)) := by
  apply (interpolationPotential_gradient_lipschitz hF x hr hl h0 h1).weaken
  apply NNReal.coe_le_coe.mp
  change 1+‖r*ρ‖*((Real.pi^2/2)*ρ*((lam:ℝ)*r))≤1+Real.pi^2/4
  rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg hr h0)]
  have hρ : ρ^2≤1 := by nlinarith
  have hh : (lam:ℝ)*r^2*ρ^2≤1/2 :=
    (mul_le_mul_of_nonneg_left hρ (by positivity)).trans (by simpa using hl)
  nlinarith [mul_le_mul_of_nonneg_left hh (sq_nonneg Real.pi)]

lemma sqrt_scaled_square (d : ℕ) {B R : ℝ} (hB : 0≤B) (hR : 0≤R) (n : ℕ) :
    Real.sqrt ((d:ℝ)*B^2*R^(2*n))=Real.sqrt (d:ℝ)*B*R^n := by
  have he : (d:ℝ)*B^2*R^(2*n)=(d:ℝ)*(B*R^n)^2 := by
    rw [mul_pow,←pow_mul]
    ring
  rw [he,Real.sqrt_mul (Nat.cast_nonneg d),Real.sqrt_sq (mul_nonneg hB (pow_nonneg hR _)),mul_assoc]

namespace TensorSum
lemma outer_slice {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r ρ : ℝ} (hr : 0 < r)
    (hlam : 0 < lam) (hl : (lam:ℝ)*r^2≤1/2) (h0 : 0≤ρ) (h1 : ρ<1)
    (A : TensorSum (Unit ⊕ Unit)) (a : Fin d) (y : Point d) :
    A.outer F x r ((lam:ℝ)*r) (fun _ => a) (ρ,y)=
      tensorAdjoint (interpolationPotential F x r ρ) (EuclideanSpace.basisFun (Fin d) ℝ)
        (fun j => A.slice F x r ρ ((lam:ℝ)*r) (Sum.elim (fun _ => a) (fun _ => j))) y := by
  exact joint_gadj_slice hF x hr.le hl h0 h1 (fun k =>
    (A.timeSmooth hF x hr hlam hl _ (ρ,y) (by dsimp; linarith) h1).differentiableAt (by simp))

theorem outer_l2 {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r ρ : ℝ} (hr : 0 < r)
    (hlam : 0 < lam) (hl : (lam:ℝ)*r^2≤1/2) (h0 : 0≤ρ) (h1 : ρ<1)
    (hd : 1≤d) (A : TensorSum (Unit ⊕ Unit)) {w : ℕ} (hw : A.weightLE w) :
    Real.sqrt (∑a : Fin d,∫y,(A.outer F x r ((lam:ℝ)*r) (fun _ => a) (ρ,y))^2 ∂interpolationLaw F x r ρ)≤
      Real.sqrt (d:ℝ)*((A.momentBudget d 1 2).toReal+
        Real.sqrt (interpolationHessianBudget:ℝ)*(A.momentBudget d 0 2).toReal)*
        ((Real.sqrt (1-ρ^2))⁻¹)^(w+1) := by
  let V : Fin d → Fin d → Point d → ℝ := fun a j =>
    A.slice F x r ρ ((lam:ℝ)*r) (Sum.elim (fun _ => a) (fun _ => j))
  have hV a j := A.slice_polySmooth hF x hr hlam hl h0 h1 (Sum.elim (fun _ => a) (fun _ => j))
  have hE := tensorAdjoint_frobenius_l2
    (interpolationPotential_smooth hF x hr.le hl h0 h1)
    (interpolationPotential_lowerTail hF x hr.le (by linarith) h0 h1)
    (interpolationPotential_gradient_uniform hF x hr.le hl h0 h1)
    (EuclideanSpace.basisFun (Fin d) ℝ) (fun a j => (hV a j).smooth)
    (fun a j => (hV a j).polyC1) (fun a i j => ((hV a j).directional _).polyC1)
  have hm := interpolationLaw_eq_gibbs hF x hr.le (by linarith) (by nlinarith : ρ^2<1)
  rw [←hm] at hE
  simp_rw [←A.outer_slice hF x hr hlam hl h0 h1] at hE
  let R := (Real.sqrt (1-ρ^2))⁻¹
  have hR0 : 0≤R := by dsimp [R]; positivity
  have hR1 : 1≤R := by
    apply (one_le_inv₀ (Real.sqrt_pos.mpr (by nlinarith))).mpr
    exact Real.sqrt_le_one.mpr (by nlinarith [sq_nonneg ρ])
  have he1 := Real.sqrt_le_sqrt (A.matrix_one_energy hF x hr hlam hl h0 h1 hd hw)
  have he0 := Real.sqrt_le_sqrt (A.matrix_zero_energy hF x hr hlam hl h0 h1 hd hw)
  rw [sqrt_scaled_square d ENNReal.toReal_nonneg hR0 (w+1)] at he1
  rw [sqrt_scaled_square d ENNReal.toReal_nonneg hR0 w] at he0
  have hp := pow_le_pow_right₀ hR1 (Nat.le_succ w)
  have hlast : Real.sqrt (d:ℝ)*(A.momentBudget d 0 2).toReal*R^w≤
      Real.sqrt (d:ℝ)*(A.momentBudget d 0 2).toReal*R^(w+1) :=
    mul_le_mul_of_nonneg_left hp (by positivity)
  apply (hE.trans (add_le_add he1 (mul_le_mul_of_nonneg_left (he0.trans hlast) (Real.sqrt_nonneg _)))).trans_eq
  dsimp only [R]
  ring
end TensorSum
end LogConcaveSampling

end

end

end

end OAI
