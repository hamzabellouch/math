import Mathlib
import OAI.Probability.SKGap.Gaussian.GaussianProductUpperTailLipschitz
import OAI.Probability.SKGap.Gaussian.GaussianProductPower

namespace OAI

section
noncomputable section
namespace SKGap
open Matrix Real MeasureTheory ProbabilityTheory Set
open scoped BigOperators Matrix.Norms.Frobenius
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]

def matrixWordSeminorm (p : Bool) (M : Matrix ι ι ℝ) : ℝ :=
  if p then offDiagonalSeminorm M else diagonalSeminorm M
lemma matrixWordSeminorm_lipschitz (p : Bool) : LipschitzWith 1 (matrixWordSeminorm (ι:=ι) p) := by
  cases p
  · exact diagonalSeminorm_lipschitz
  · exact offDiagonalSeminorm_lipschitz
lemma matrixWordSeminorm_add (p : Bool) (M N : Matrix ι ι ℝ) :
    matrixWordSeminorm p (M+N)≤ matrixWordSeminorm p M+matrixWordSeminorm p N := by
  cases p
  · exact diagonalSeminorm_add M N
  · exact offDiagonalSeminorm_add M N
lemma matrixWordSeminorm_nonneg (p : Bool) (M : Matrix ι ι ℝ) : 0≤ matrixWordSeminorm p M := by
  let : Fact (1≤(4:ENNReal)) := ⟨by norm_num⟩
  cases p
  · exact norm_nonneg (diagonalVector M)
  · exact norm_nonneg (offDiagonalVector M)

lemma matrixCentered_sub {F G : EuclideanSpace ℝ κ→Matrix ι ι ℝ}
    {L K : NNReal} (hF : LipschitzWith L F) (hG : LipschitzWith K G) (x : EuclideanSpace ℝ κ) :
    matrixCentered (fun y=>F y-G y) x=matrixCentered F x-matrixCentered G x := by
  have hm : matrixEntryMean (fun y=>F y-G y)=matrixEntryMean F-matrixEntryMean G := by
    ext i k
    exact integral_sub (gaussianProduct_integrable_lipschitz (matrixEntry_lip hF i k))
      (gaussianProduct_integrable_lipschitz (matrixEntry_lip hG i k))
  simp only [matrixCentered,hm]
  abel

lemma gaussianProduct_centered_matrix_tail {F : EuclideanSpace ℝ κ→Matrix ι ι ℝ}
    {L : NNReal} (hF : LipschitzWith L F) (hL : 0<L) (p : Bool) {u : ℝ} (hu : 0≤u) :
    (Measure.pi (fun _ : κ=>gaussianReal 0 1))
      {g | matrixNormConstant*sqrt (Fintype.card ι)*(L:ℝ)+u<
        matrixWordSeminorm p (matrixCentered F (WithLp.toLp 2 g))}≤
      ENNReal.ofReal (exp (-2*u^2/(π^2*(L:ℝ)^2))) := by
  let μ := Measure.pi (fun _ : κ=>gaussianReal 0 1)
  let X : (κ→ℝ)→ℝ := fun g=>matrixWordSeminorm p (matrixCentered F (WithLp.toLp 2 g))
  have hXL : LipschitzWith L (fun x : EuclideanSpace ℝ κ=>X x.ofLp) := by
    simpa only [X,WithLp.toLp_ofLp,one_mul,Function.comp_def] using
      (matrixWordSeminorm_lipschitz p).comp (matrixCentered_lipschitz hF)
  have hE : (∫ g,X g ∂μ)≤ matrixNormConstant*sqrt (Fintype.card ι)*(L:ℝ) := by
    cases p
    · exact (gaussianProduct_centered_matrix_norms hF hL).1
    · exact (gaussianProduct_centered_matrix_norms hF hL).2
  have htail := gaussianProduct_upper_tail_lipschitz hXL hL hu
  have hmono : μ {g | matrixNormConstant*sqrt (Fintype.card ι)*(L:ℝ)+u<X g}≤
      μ {g | u≤X g-∫ h,X h ∂μ} := by
    apply measure_mono
    intro g hg
    change matrixNormConstant*sqrt (Fintype.card ι)*(L:ℝ)+u<X g at hg
    change u≤X g-∫ h,X h ∂μ
    linarith only [hg,hE]
  apply hmono.trans
  rw [←ENNReal.ofReal_toReal (measure_ne_top μ _)]
  exact ENNReal.ofReal_le_ofReal htail
end SKGap
end
end

section
noncomputable section
namespace SKGap
open Matrix Real MeasureTheory ProbabilityTheory Set
open scoped BigOperators Matrix.Norms.Frobenius
variable {κ : Type*} [Fintype κ]

lemma gaussianMatrix_scaled_semnorm_tail {n : ℕ} (hn : 1 ≤ n)
    {F : EuclideanSpace ℝ κ→Matrix (Fin n) (Fin n) ℝ} {H r T s : ℝ}
    (hH : 0<H) (hr : 0<r) (hT : 0 ≤ T) (hs : 0 ≤ s)
    (hF : LipschitzWith (Real.toNNReal (H*r/sqrt n)) F) (p : Bool) :
    (Measure.pi (fun _ : κ=>gaussianReal 0 1))
      {g | (matrixNormConstant*H+T*s)*r< matrixWordSeminorm p (matrixCentered F (WithLp.toLp 2 g))} ≤
      ENNReal.ofReal (exp (-2*T^2*s^2*(n:ℝ)/(π^2*H^2))) := by
  have hn0 : (0:ℝ)<n := by exact_mod_cast (show 0<n by omega)
  have hnS := sqrt_pos.mpr hn0
  have hL : 0<Real.toNNReal (H*r/sqrt n) := by exact_mod_cast (Real.toNNReal_pos.mpr (div_pos (mul_pos hH hr) hnS))
  have hh := gaussianProduct_centered_matrix_tail hF hL p (mul_nonneg (mul_nonneg hT hs) hr.le)
  have he : (matrixNormConstant*sqrt (Fintype.card (Fin n))*(Real.toNNReal (H*r/sqrt n):ℝ)+T*s*r)=
      (matrixNormConstant*H+T*s)*r := by
    rw [Fintype.card_fin,Real.coe_toNNReal _ (by positivity)]
    field_simp
  have he' : -2*(T*s*r)^2/(π^2*(Real.toNNReal (H*r/sqrt n):ℝ)^2)=
      -2*T^2*s^2*(n:ℝ)/(π^2*H^2) := by
    rw [Real.coe_toNNReal _ (by positivity)]
    field_simp
    rw [sq_sqrt hn0.le]
  rw [he,he'] at hh
  exact hh
end SKGap
end
end

end OAI
