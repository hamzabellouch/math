import OAI.Analysis.NumericalRange.DensityComparison

namespace OAI

universe u_258

section
noncomputable section
open Set Filter Metric Complex MeasureTheory
open scoped Matrix Topology ComplexConjugate ComplexOrder MatrixOrder Matrix.Norms.L2Operator Kronecker
namespace CompleteCrouzeix
variable {n : Type u_258} [Fintype n] [DecidableEq n] [Nonempty n]
lemma matrix_contractivity_iff {n : Type u_258} [Fintype n] [DecidableEq n] [Nonempty n]
    (B : Matrix n n ℂ) : Bᴴ*B ≤ 1 ↔ ‖B‖ ≤ 1 := by
  have hn := CStarAlgebra.norm_le_one_iff_of_nonneg (Bᴴ*B)
    (Matrix.posSemidef_conjTranspose_mul_self B).nonneg
  rw [Matrix.l2_opNorm_conjTranspose_mul_self] at hn
  constructor
  · intro h
    have hh := hn.mpr h
    nlinarith [norm_nonneg B]
  · intro h
    apply hn.mp
    nlinarith [norm_nonneg B]
lemma metric_sqrt_inverse_contraction {H : Matrix n n ℂ} (hp : H.PosDef) (hH : 1 ≤ H) :
    ‖(CFC.sqrt H)⁻¹‖ ≤ 1 := by
  let S := CFC.sqrt H
  have hS : S.IsHermitian := (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg H)).isHermitian
  have hS2 : S*S = H := CFC.sqrt_mul_sqrt_self H hp.posSemidef.nonneg
  have hu : IsUnit S.det := (Matrix.isUnit_iff_isUnit_det S).mp (metric_sqrt_isUnit hp)
  have hi : S⁻¹*S = 1 := Matrix.nonsing_inv_mul S hu
  have hi' : S*S⁻¹ = 1 := Matrix.mul_nonsing_inv S hu
  have hpos := (Matrix.nonneg_iff_posSemidef.mp (sub_nonneg.mpr hH)).conjTranspose_mul_mul_same S⁻¹
  have hid : S⁻¹ᴴ*(H-1)*S⁻¹ = 1-S⁻¹ᴴ*S⁻¹ := by
    rw [Matrix.mul_sub,Matrix.sub_mul,Matrix.mul_one,hS.inv.eq,← hS2]
    rw [← Matrix.mul_assoc,hi,Matrix.one_mul,hi']
  rw [hid] at hpos
  exact (matrix_contractivity_iff S⁻¹).mp hpos
lemma metric_sqrt_norm_le {T H : Matrix n n ℂ} {τ : ℝ}
    (hf : MetricFeasible T τ H) (hp : H.PosDef) : ‖CFC.sqrt H‖ ≤ Real.sqrt τ := by
  have hS : (CFC.sqrt H).IsHermitian :=
    (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg H)).isHermitian
  have hsq := Matrix.l2_opNorm_conjTranspose_mul_self (CFC.sqrt H)
  rw [hS.eq,CFC.sqrt_mul_sqrt_self H hp.posSemidef.nonneg] at hsq
  have hτ : 0 ≤ τ := zero_le_one.trans hf.one_le
  have hs := Real.sq_sqrt hτ
  have hnorm := hf.norm_le
  nlinarith [Real.sqrt_nonneg τ,norm_nonneg (CFC.sqrt H)]
lemma metric_condition_estimate {T H : Matrix n n ℂ} {τ : ℝ}
    (hf : MetricFeasible T τ H) (hp : H.PosDef) :
    ‖CFC.sqrt H‖ * ‖(CFC.sqrt H)⁻¹‖ ≤ Real.sqrt τ := by
  calc
    _ ≤ ‖CFC.sqrt H‖*1 := mul_le_mul_of_nonneg_left (metric_sqrt_inverse_contraction hp hf.1) (norm_nonneg _)
    _ ≤ _ := by simpa only [mul_one] using metric_sqrt_norm_le hf hp
end CompleteCrouzeix

end

end

end OAI
