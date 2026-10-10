import Mathlib
import OAI.Probability.SKGap.Matrix.LogDetIntegral

namespace OAI

section
noncomputable section
namespace SKGap
open Matrix MeasureTheory ProbabilityTheory Real Set Filter
open scoped BigOperators Matrix.Norms.Frobenius NNReal Topology
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma regularizedLogDet_lipschitzWith [Nonempty ι] {γ : ℝ} (hγ : 0 < γ) :
    LipschitzWith ⟨1/sqrt ((Fintype.card ι:ℝ)*γ),by positivity⟩
      (LogDet.regularizedLogDet γ : Matrix ι ι ℝ → ℝ) := by
  apply LipschitzWith.of_dist_le_mul
  intro M N
  change |LogDet.regularizedLogDet γ M-LogDet.regularizedLogDet γ N| ≤
    (1/sqrt ((Fintype.card ι:ℝ)*γ))*‖M-N‖
  exact LogDet.regularizedLogDet_lipschitz hγ M N

lemma logPath_regularized_tail [Nonempty ι] {j γ u : ℝ} (hj : 0 < j) (hγ : 0 < γ)
    (hu : 0 ≤ u) {a : ι → ℝ} (ha : ∀ i, 0 ≤ a i) (ha1 : ∀ i, a i ≤ 1) :
    let F := fun g => LogDet.regularizedLogDet γ (logPath ((j/(Fintype.card ι:ℝ))*∑ i,a i) a
      (goeMatrix (j/(Fintype.card ι:ℝ)) g) 1)
    let μ := Measure.pi (fun _ : MatrixCoordinates ι => gaussianReal 0 1)
    μ.real {g | u ≤ |F g-∫ x,F x ∂μ|} ≤
      2*Real.exp (-γ*(Fintype.card ι:ℝ)^2*u^2/(π^2*j)) := by
  have hn : (0:ℝ) < Fintype.card ι := Nat.cast_pos.mpr Fintype.card_pos
  have hc := (regularizedLogDet_lipschitzWith hγ).comp
    ((logPath_one_lipschitz (j := j) ha ha1).comp (goeMatrix_L2_lipschitz (j/(Fintype.card ι:ℝ))))
  let L : ℝ≥0 := ⟨(1/sqrt ((Fintype.card ι:ℝ)*γ))*sqrt (2*(j/(Fintype.card ι:ℝ))),by positivity⟩
  have hc' : LipschitzWith L (fun x : EuclideanSpace ℝ (MatrixCoordinates ι) =>
      LogDet.regularizedLogDet γ (logPath ((j/(Fintype.card ι:ℝ))*∑ i,a i) a
        (goeMatrix (j/(Fintype.card ι:ℝ)) x.ofLp) 1)) := by
    exact hc.weaken (by
      change (1/sqrt ((Fintype.card ι:ℝ)*γ))*(1*sqrt (2*(j/(Fintype.card ι:ℝ)))) ≤
        (1/sqrt ((Fintype.card ι:ℝ)*γ))*sqrt (2*(j/(Fintype.card ι:ℝ)))
      rw [_root_.one_mul])
  have hL : 0 < L := NNReal.coe_pos.mp (by
    change 0 < (1/sqrt ((Fintype.card ι:ℝ)*γ))*sqrt (2*(j/(Fintype.card ι:ℝ)))
    exact mul_pos (one_div_pos.mpr (sqrt_pos.mpr (mul_pos hn hγ)))
      (sqrt_pos.mpr (mul_pos (by norm_num) (div_pos hj hn))))
  have h := gaussianProduct_tail_lipschitz
    (f := fun g => LogDet.regularizedLogDet γ (logPath ((j/(Fintype.card ι:ℝ))*∑ i,a i) a
      (goeMatrix (j/(Fintype.card ι:ℝ)) g) 1)) hc' hL hu
  apply h.trans_eq
  congr 2
  change -2*u^2/(π^2*((1/sqrt ((Fintype.card ι:ℝ)*γ))*sqrt (2*(j/(Fintype.card ι:ℝ))))^2)=_
  rw [mul_pow,_root_.one_div_pow,sq_sqrt (by positivity : 0 ≤ (Fintype.card ι:ℝ)*γ),
    sq_sqrt (by positivity : 0 ≤ 2*(j/(Fintype.card ι:ℝ)))]
  field_simp

lemma regularizedLogDet_transpose {γ : ℝ} (hγ : γ ≠ 0) (M : Matrix ι ι ℝ) :
    LogDet.regularizedLogDet γ Mᵀ=LogDet.regularizedLogDet γ M := by
  have e₁ : γ • (1+(γ⁻¹ • M)*Mᵀ)=M*Mᵀ+γ • 1 := by
    rw [smul_add,smul_mul_assoc,smul_smul,mul_inv_cancel₀ hγ,one_smul]
    ac_rfl
  have e₂ : γ • (1+Mᵀ*(γ⁻¹ • M))=Mᵀ*M+γ • 1 := by
    rw [smul_add,mul_smul_comm,smul_smul,mul_inv_cancel₀ hγ,one_smul]
    ac_rfl
  unfold LogDet.regularizedLogDet LogDet.regularizedGram
  rw [transpose_transpose,← e₁,← e₂,det_smul,det_smul,det_one_add_mul_comm]
end SKGap
end
end

end OAI
