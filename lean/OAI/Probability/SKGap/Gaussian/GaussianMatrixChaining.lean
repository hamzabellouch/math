import Mathlib
import OAI.Probability.SKGap.Gaussian.MatrixNormTail
import OAI.Probability.SKGap.Localization.BoxChaining

namespace OAI

section
noncomputable section
namespace SKGap
open Matrix Real MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators Matrix.Norms.Frobenius Topology
variable {κ α : Type*} [Fintype κ] [Fintype α] [DecidableEq α]

def gaussianMatrixChainConstant (H B : ℝ) : ℝ :=
  5*(matrixNormConstant*H+π*H*sqrt (B+1))

lemma gaussianMatrixChain_exponent {H B s : ℝ} (hH : 0<H) (hB : 0 ≤ B) (n : ℕ) :
    -2*(π*H*sqrt (B+1))^2*s^2*(n:ℝ)/(π^2*H^2)=
      -(2*(B+1))*s^2*(n:ℝ) := by
  rw [mul_pow,mul_pow,sq_sqrt (by linarith : 0 ≤ B+1)]
  field_simp

theorem gaussianMatrix_box_chaining {n : ℕ} (hn : 1 ≤ n) {H B : ℝ}
    (hH : 0<H) (hB : 0 ≤ B) (hdim : log 16*(Fintype.card α:ℝ) ≤ B*(n:ℝ))
    (F : (α→Icc (0:ℝ) 1)→EuclideanSpace ℝ κ→Matrix (Fin n) (Fin n) ℝ)
    (hF : ∀ θ,LipschitzWith (Real.toNNReal (H/sqrt n)) (F θ))
    (hi : ∀ k θ η,dist θ η ≤ 2*(1/4:ℝ)^k→
      LipschitzWith (Real.toNNReal (H*(1/2:ℝ)^k/sqrt n)) (fun x=>F θ x-F η x))
    (hc : ∀ g : κ→ℝ,Continuous (fun θ=>matrixCentered (F θ) (WithLp.toLp 2 g)))
    (p : Bool) :
    (Measure.pi (fun _ : κ=>gaussianReal 0 1))
      {g | ∃ θ,gaussianMatrixChainConstant H B< matrixWordSeminorm p (matrixCentered (F θ) (WithLp.toLp 2 g))} ≤
      ENNReal.ofReal (3*exp (-(n:ℝ))) := by
  let T := π*H*sqrt (B+1)
  let b := matrixNormConstant*H+T
  have hT : 0 ≤ T := by dsimp [T];positivity
  have hC : 0 ≤ matrixNormConstant := zero_le_one.trans matrixNormConstant_bounds.1
  have hb0 : 0 ≤ b := add_nonneg (mul_nonneg hC hH.le) hT
  let r : ℕ→ℝ := fun k=>b*((k:ℝ)+1)*(1/2:ℝ)^k
  have hsum : HasSum r (b*4) := by
    have he : r=(fun k : ℕ=>b*(((k:ℝ)+1)*(1/2:ℝ)^k)) := by
      funext k
      dsimp [r]
      ring
    rw [he]
    exact arithmetic_half_geometric_hasSum.mul_left b
  have hbase (θ : α→Icc (0:ℝ) 1) : (Measure.pi (fun _ : κ=>gaussianReal 0 1))
      {g | b< matrixWordSeminorm p (matrixCentered (F θ) (WithLp.toLp 2 g))} ≤
      ENNReal.ofReal (exp (-(2*(B+1))*(n:ℝ))) := by
    have hh := gaussianMatrix_scaled_semnorm_tail hn hH (by norm_num : (0:ℝ)<1) hT
      (by norm_num : (0:ℝ) ≤ 1) (F:=F θ) (by simpa only [mul_one] using hF θ) p
    rw [gaussianMatrixChain_exponent hH hB] at hh
    simpa only [T,b,mul_one,one_pow] using hh
  have hincr (k : ℕ) (θ η : α→Icc (0:ℝ) 1) (hθ : dist θ η ≤ 2*(1/4:ℝ)^k) :
      (Measure.pi (fun _ : κ=>gaussianReal 0 1))
      {g | r k< matrixWordSeminorm p (matrixCentered (F θ) (WithLp.toLp 2 g)-matrixCentered (F η) (WithLp.toLp 2 g))} ≤
      ENNReal.ofReal (exp (-(2*(B+1))*((k:ℝ)+1)^2*(n:ℝ))) := by
    have hh := gaussianMatrix_scaled_semnorm_tail hn hH (by positivity : (0:ℝ)<(1/2:ℝ)^k) hT
      (by positivity : 0 ≤ (k:ℝ)+1) (hi k θ η hθ) p
    rw [gaussianMatrixChain_exponent hH hB] at hh
    simp_rw [matrixCentered_sub (hF θ) (hF η)] at hh
    apply (measure_mono (show {g | r k< matrixWordSeminorm p (matrixCentered (F θ) (WithLp.toLp 2 g)-matrixCentered (F η) (WithLp.toLp 2 g))}⊆
      {g | (matrixNormConstant*H+T*((k:ℝ)+1))*(1/2:ℝ)^k< matrixWordSeminorm p (matrixCentered (F θ) (WithLp.toLp 2 g)-matrixCentered (F η) (WithLp.toLp 2 g))} from ?_)).trans hh
    intro g hg
    change r k<_ at hg
    change (matrixNormConstant*H+T*((k:ℝ)+1))*(1/2:ℝ)^k<_
    apply lt_of_le_of_lt _ hg
    dsimp [r,b]
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    nlinarith only [mul_nonneg (mul_nonneg hC hH.le) (Nat.cast_nonneg k)]
  have hh := box_chaining_probability (Measure.pi (fun _ : κ=>gaussianReal 0 1))
    (matrixWordSeminorm p) (matrixWordSeminorm_lipschitz p).continuous (matrixWordSeminorm_add p)
    (fun θ g=>matrixCentered (F θ) (WithLp.toLp 2 g)) hc hn hB (by linarith : B+1 ≤ 2*(B+1))
    hdim b r (fun k=>by dsimp [r];positivity) hsum.summable hbase hincr
  rw [hsum.tsum_eq] at hh
  have he : b+b*4=gaussianMatrixChainConstant H B := by dsimp [b,T,gaussianMatrixChainConstant];ring
  rwa [he] at hh
end SKGap
end
end

end OAI
