import OAI.Geometry.Convex.GeneralMahler.HLayer

namespace OAI
/-! Uniform cone hypotheses for the full-real-line estimates.
The extra constants are not inputs to main theorems: for every field
such bounds exist. -/
noncomputable section
open Set Filter Real MeasureTheory MeasureTheory.Measure Metric
open scoped ENNReal NNReal Topology MatrixOrder Matrix.Norms.L2Operator RealInnerProductSpace
namespace GeneralMahler
open Layers
variable {m : ℕ}
namespace ProjField

structure Bound (q : ProjField m) (K : ℝ) : Prop where
  one_le : 1 ≤ K
  Ub : ‖q.U‖ ≤ K
  Vb : ‖q.V‖ ≤ K
  S_le : ‖q.S‖ ≤ K
  iS_le : ‖q.root.symm.toContinuousLinearMap‖ ≤ K
  inC : ∀ x ∈ q.D, ‖x‖ ≤ K*⟪q.U,x⟫
  inD : ∀ x ∈ q.C, ‖x‖ ≤ K*⟪q.V,x⟫

variable {q : ProjField m} {K : ℝ} (hK : q.Bound K)

include hK in
lemma Bound.positive : 0 < K := lt_of_lt_of_le zero_lt_one hK.one_le

variable (q) in
theorem Field_isBound : ∃ K, q.Bound K := by
  obtain ⟨c,hc,h₁⟩ := interior_dual_bound q.V_in
  obtain ⟨d,hd,h₂⟩ := interior_dual_bound (C := q.D)
    (V := q.U) (by rw [show posDual q.D = q.C from ProperCone.innerDual_innerDual _]; exact q.U_in)
  let K := (1+‖q.U‖+‖q.V‖+‖q.S‖+‖q.root.symm.toContinuousLinearMap‖) + c⁻¹ + d⁻¹
  have hnorm (n : ℝ) (hn : n ≤ 1+‖q.U‖+‖q.V‖+‖q.S‖+‖q.root.symm.toContinuousLinearMap‖) :
      n ≤ K := by
    dsimp [K]; have h : 0 ≤ c⁻¹+d⁻¹ := by positivity
    linarith
  have he : c⁻¹ ≤ K ∧ d⁻¹ ≤ K := by
    dsimp [K]
    constructor <;> rw [← sub_nonneg] <;> ring_nf <;> positivity
  have hu := norm_nonneg q.U
  have hv := norm_nonneg q.V
  have hh := norm_nonneg q.S
  have ha := norm_nonneg q.root.symm.toContinuousLinearMap
  refine ⟨K, hnorm _ (by linarith),hnorm _ (by linarith), hnorm _ (by linarith),
    hnorm _ (by linarith), hnorm _ (by linarith),fun x hx => ?_,fun x hx => ?_⟩
  · have hb := h₂ x hx
    have hp : 0 ≤ ⟪q.U,x⟫ := le_trans (by positivity) hb
    apply le_trans _ (mul_le_mul_of_nonneg_right he.2 hp)
    rw [le_inv_mul_iff₀ hd]; exact hb
  · have hb := h₁ x hx
    have hp : 0 ≤ ⟪q.V,x⟫ := le_trans (by positivity) hb
    apply le_trans _ (mul_le_mul_of_nonneg_right he.1 hp)
    rw [le_inv_mul_iff₀ hc]; exact hb

include hK in
lemma Bound.normZ (x : Rn m) : ‖q.Z x‖ ≤ K * ‖x‖ := calc
  _ ≤ ‖q.S‖*‖x‖ := by rw [q.Z_def]; exact (op q.S).le_opNorm _
  _ ≤ _ := mul_le_mul_of_nonneg_right hK.S_le (norm_nonneg _)

section
variable (q)

lemma X_int (z : ℝ) : Integrable (q.XT z) (normal m) := sample_integrable ..
lemma Y_int (z : ℝ) : Integrable (q.YT z) (normal m) := by
  rw [funext (q.YT_sub z)]
  exact (q.X_int z).sub (affineN_integrable ..)

lemma avH_le_s (z : ℝ) : q.avH z ≤ q.s0 := by
  unfold avH s0 trN
  have hi := mean_lt_one q.C q.root ⟨_,q.V_in⟩ (q.shift z)
  gcongr
  have hh := Matrix.le_iff.mpr hi.posSemidef
  conv_rhs => rw [← mul_one q.covMat]
  rw [q.trace_SPS,q.trace_SPS]
  exact Finset.sum_le_sum fun i _ =>
    op_order_iff (mean_pos q.C q.root ⟨_,q.U_in⟩ _).1 Matrix.isHermitian_one |>.mp hh _

lemma Bt_cd : ContDiff ℝ 1 q.Bt := by
  have he : q.Bt = fun z => ⟪q.U,a z • q.U-q.shift z⟫/(m:ℝ) := funext fun z => by rw [Bt,q.Y_mean]
  rw [he]
  exact ((contDiff_const.inner ℝ ((contDiff_a.smul contDiff_const).sub q.shift_cd))).div_const _

end
section
variable [NeZero m]
lemma m_pos : 0 < (m:ℝ) := by exact_mod_cast (Nat.pos_of_ne_zero (NeZero.ne m))

include hK in
lemma Bound.s0_le : q.s0 ≤ K^2 := by
  unfold s0 trN
  rw [div_le_iff₀ m_pos,← mul_one q.covMat,q.trace_SPS]
  let b := EuclideanSpace.basisFun (Fin m) ℝ
  apply le_trans (Finset.sum_le_sum (g := fun i => K^2) ?_)
  · simp; rw [mul_comm]
  intro i hi
  rw [_root_.map_one]
  change ⟪op q.S (b i), op q.S (b i)⟫ ≤ _
  have hn : ‖b i‖ = 1 := b.orthonormal.1 i
  rw [← Z_def,real_inner_self_eq_norm_sq]
  have hh := hK.normZ (b i)
  rw [hn,mul_one] at hh
  gcongr

include hK in
omit [NeZero m] in
lemma Bound.X_mean (z : ℝ) :
    (∫ x, ‖q.XT z x‖ ∂normal m) ≤ K*m*a z := by
  let l : Rn m →L[ℝ] ℝ := innerSL ℝ q.V
  have hi := q.X_int z
  calc
    _ ≤ ∫ x, K*l (q.XT z x) ∂normal m :=
      integral_mono hi.norm ((l.integrable_comp hi).const_mul K)
        (fun x => hK.inD (q.XT z x) (proj_mem ..))
    _ = _ := by
      rw [integral_const_mul,l.integral_comp_comm hi,q.XT_mean]
      change K*⟪q.V,a z • q.U⟫=_
      rw [real_inner_smul_right,real_inner_comm,q.ip]
      ring

include hK in
lemma Bound.Y_mean (z : ℝ) :
    (∫ x, ‖q.YT z x‖ ∂normal m) ≤ K*m*q.Bt z := by
  let l : Rn m →L[ℝ] ℝ := innerSL ℝ q.U
  have hi := q.Y_int z
  calc
    _ ≤ ∫ x, K*l (q.YT z x) ∂normal m :=
      integral_mono hi.norm ((l.integrable_comp hi).const_mul K)
        (fun x => hK.inC (q.YT z x) (proj_mem ..))
    _ = _ := by
      rw [integral_const_mul,l.integral_comp_comm hi]
      dsimp [l,Bt]; have H := m_pos (m := m); field_simp

omit [NeZero m] in
lemma mul_Bt_avH (q : ProjField m) (z : ℝ) : a z * q.Bt z ≤ q.avH z := by
  rw [q.avH_variance]; exact le_add_of_nonneg_left (div_nonneg
    (integral_nonneg (fun x => sq_nonneg _)) (Nat.cast_nonneg _))

include hK in
omit [NeZero m] in
lemma XT_lip' (x y : Rn m) (z : ℝ) :
    ‖q.XT z x-q.XT z y‖ ≤ K * ‖x-y‖ := by
  apply le_trans _ (hK.normZ (x-y))
  have he : affineN q.root (q.shift z) x-affineN q.root (q.shift z) y = q.Z (x-y) := by
    unfold affineN Z; rw [_root_.map_sub]; abel
  rw [← he]
  simpa only [XT,sample,dist_eq_norm, NNReal.coe_one,one_mul] using (coneProj_lip q.C).dist_le_mul
    (affineN q.root (q.shift z) x) (affineN q.root (q.shift z) y)

include hK in
omit [NeZero m] in
lemma YT_lip' (x y : Rn m) (z : ℝ) :
    ‖q.YT z x-q.YT z y‖ ≤ K * ‖x-y‖ := by
  let f := fun x => -(q.Z x + q.shift z)
  have he : f x-f y = -(q.Z (x-y)) := by unfold f Z; rw [_root_.map_sub]; abel
  have h := (coneProj_lip q.D).dist_le_mul (f x) (f y)
  rw [dist_eq_norm,dist_eq_norm,NNReal.coe_one, one_mul,he,norm_neg] at h
  exact h.trans (hK.normZ _)
end

def J (m : ℕ) := ∫ x : Rn m, ‖x‖ ∂normal m

lemma i_norm (m : ℕ) : Integrable (fun x : Rn m => ‖x‖) (normal m) :=
  (ProbabilityTheory.IsGaussian.integrable_id (μ := normal m)).norm
lemma j_nonneg (m : ℕ) : 0 ≤ J m := integral_nonneg fun _x => norm_nonneg _

-- Bounding a Lipschitz map by its mean absolute norm
lemma norm_le_mean_error {E:Type*} [NormedAddCommGroup E] {F : Rn m → E} {K : ℝ}
    (hf : Integrable F (normal m)) (hl : ∀ x y, ‖F x - F y‖ ≤ K*‖x-y‖)
    (hk : 0 ≤ K) (x : Rn m) :
    ‖F x‖ ≤ (∫ x, ‖F x‖ ∂normal m)+ K*(‖x‖+J m) := by
  let μ := normal m
  have hg : Integrable (fun y : Rn m => (‖x‖+‖y‖)) μ :=
    (integrable_const _).add (i_norm _)
  calc
    _ = ∫ y:Rn m, ‖F x‖ ∂μ := by dsimp [μ]; simp
    _ ≤ ∫ y:Rn m, (‖F y‖ + K*(‖x‖+‖y‖)) ∂μ := integral_mono (integrable_const _)
      (hf.norm.add (hg.const_mul K)) (fun y => by
        have hh := norm_add_le (F x-F y) (F y)
        rw [sub_add_cancel] at hh
        nlinarith [norm_sub_le x y, hl x y])
    _ = _ := by
      rw [integral_add hf.norm (hg.const_mul _),integral_const_mul, integral_add
        (integrable_const _) (i_norm _)]
      dsimp [μ,J]; simp
end ProjField
end GeneralMahler

end

end OAI
