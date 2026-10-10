import Mathlib
import OAI.Combinatorics.KMedianRecovery.Recovery.SqNorm

namespace OAI

namespace MetricKMedianRecovery.Ellipsoid
open Matrix
open scoped Matrix
variable {V : Type*} [Fintype V] [DecidableEq V]

omit [DecidableEq V] in
lemma hermitian_vecMul (H : Matrix V V ℝ) (hH : H.IsHermitian) (a : V → ℝ) :
    a ᵥ* H=H *ᵥ a := by
  have ht : Hᵀ=H := (isHermitian_iff_isSymm.mp hH).eq
  simpa only [ht] using (vecMul_transpose H a)

lemma rank_one_shape_inverse (H : Matrix V V ℝ) (hH : H.PosDef) (a : V → ℝ)
    (c : ℝ) (hc : 1+c*quad H a≠0) :
    (H⁻¹+c • vecMulVec a a)⁻¹=
      H-(c/(1+c*quad H a)) • vecMulVec (H *ᵥ a) (H *ᵥ a) := by
  apply Matrix.inv_eq_right_inv
  have hv : H⁻¹ *ᵥ (H *ᵥ a)=a := by
    rw [mulVec_mulVec,nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hH.det_pos.ne'),one_mulVec]
  rw [mul_sub,add_mul,add_mul,nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hH.det_pos.ne'),
    smul_mul_assoc,mul_smul_comm,mul_smul_comm,smul_mul_assoc,
    mul_vecMulVec,hv,vecMulVec_mul,hermitian_vecMul H hH.isHermitian a,
    vecMulVec_mul_vecMulVec,vecMulVec_smul,smul_smul]
  ext i j
  simp only [Matrix.add_apply,Matrix.sub_apply,Matrix.smul_apply,smul_eq_mul,vecMulVec_apply]
  unfold quad at hc ⊢
  field_simp
  ring

noncomputable def normalizedDual (H : Matrix V V ℝ) (a : V → ℝ) : V → ℝ :=
  (1/Real.sqrt (quad H a)) • (H *ᵥ a)

lemma dual_normal_properties (H : Matrix V V ℝ) (hH : H.PosDef) (a : V → ℝ) (ha : a≠0) :
    0<quad H a ∧ quad H⁻¹ (normalizedDual H a)=1 ∧
    H⁻¹ *ᵥ normalizedDual H a=(1/Real.sqrt (quad H a)) • a := by
  have hq : 0<quad H a := by
    simpa only [quad,star_trivial] using hH.dotProduct_mulVec_pos ha
  have hs : Real.sqrt (quad H a)≠0 := (Real.sqrt_pos.2 hq).ne'
  have hv : H⁻¹ *ᵥ (H *ᵥ a)=a := by
    rw [mulVec_mulVec,nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hH.det_pos.ne'),one_mulVec]
  refine ⟨hq,?_,?_⟩
  · rw [normalizedDual,quad_smul_vec]
    have he : quad H⁻¹ (H *ᵥ a)=quad H a := by
      unfold quad
      rw [hv,dotProduct_comm]
    rw [he,div_pow,one_pow,Real.sq_sqrt hq.le]
    field_simp
  · simp only [normalizedDual,mulVec_smul,hv]

noncomputable def cutShape (d : ℝ) (H : Matrix V V ℝ) (a : V → ℝ) : Matrix V V ℝ :=
  (d^2/(d^2-1)) • (H-(2/((d+1)*quad H a)) • vecMulVec (H *ᵥ a) (H *ᵥ a))

lemma cutShape_inverse (d : ℝ) (hd : 1<d) (H : Matrix V V ℝ) (hH : H.PosDef)
    (a : V → ℝ) (ha : a≠0) :
    cutShape d H a=(cutMatrix d H⁻¹ (normalizedDual H a))⁻¹ := by
  obtain ⟨hq,hu,hv⟩ := dual_normal_properties H hH a ha
  have hd0 : d≠0 := by linarith
  have hdm : d-1≠0 := by linarith
  have hdp : d+1≠0 := by linarith
  have hds : d^2-1≠0 := by nlinarith
  have hs : Real.sqrt (quad H a)≠0 := (Real.sqrt_pos.2 hq).ne'
  have he : cutMatrix d H⁻¹ (normalizedDual H a)=
      ((d^2-1)/d^2) • (H⁻¹+(2/((d-1)*quad H a)) • vecMulVec a a) := by
    unfold cutMatrix
    rw [hv,smul_vecMulVec,vecMulVec_smul,smul_smul,smul_smul,smul_add,smul_smul]
    congr 1
    congr 1
    have hs2 := Real.sq_sqrt hq.le
    field_simp
    nlinarith
  have hc : 1+2/((d-1)*quad H a)*quad H a≠0 := by
    have hh : 1+2/((d-1)*quad H a)*quad H a=(d+1)/(d-1) := by field_simp; ring
    rw [hh]
    exact div_ne_zero hdp hdm
  have hinner : (H⁻¹+(2/((d-1)*quad H a)) • vecMulVec a a).PosDef := by
    have hp := cutMatrix_pos d hd H⁻¹ hH.inv (normalizedDual H a)
    rw [he] at hp
    have hscale : (0:ℝ)<d^2/(d^2-1) := div_pos (by positivity) (by nlinarith)
    have hh := hp.smul hscale
    have hid : d^2/(d^2-1)*((d^2-1)/d^2)=(1:ℝ) := by field_simp
    simpa only [smul_smul,hid,one_smul] using hh
  rw [he,inv_smul_real _ hinner _ (div_ne_zero hds (pow_ne_zero _ hd0)),
    rank_one_shape_inverse H hH a _ hc]
  have hcoeff : 2/((d+1)*quad H a) =
      (2/((d-1)*quad H a))/(1+2/((d-1)*quad H a)*quad H a) := by
    apply (eq_div_iff hc).mpr
    field_simp
    ring
  simp only [cutShape,inv_div,hcoeff]

end MetricKMedianRecovery.Ellipsoid

end OAI
