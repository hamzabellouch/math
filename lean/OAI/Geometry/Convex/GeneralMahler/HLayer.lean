import OAI.Geometry.Convex.GeneralMahler.Field

namespace OAI
/-! Equation (6): projection integration by parts; derivative
of the cumulative scalar layer kernel. -/
noncomputable section
open Set Filter MeasureTheory MeasureTheory.Measure Real Matrix
open scoped ENNReal NNReal Topology MatrixOrder Matrix.Norms.L2Operator RealInnerProductSpace
namespace GeneralMahler
open Layers
variable {m : ℕ}

local notation "std" => EuclideanSpace.basisFun (Fin m) ℝ

lemma trace_op (A : Mat m) :
    trace A = ∑ i, ⟪std i,op A (std i)⟫ := by
  simp_rw [inner_toEuclideanCLM]
  unfold trace
  apply Finset.sum_congr rfl; intro i _
  simp [dotProduct,mulVec,EuclideanSpace.basisFun_apply,EuclideanSpace.single]

namespace ProjField
variable (q : ProjField m)

def avH (z : ℝ) : ℝ := trN (q.covMat * meanJac q.C q.root (q.shift z))
def s0 := trN q.covMat

lemma Z_def (x) : q.Z x = op q.S x := congrFun (congrArg DFunLike.coe q.matrix_eq) x

lemma XT_lipschitz (z : ℝ) : ∃ K, LipschitzWith K (q.XT z) := by
  exact ⟨_,(coneProj_lip q.C).comp ((q.root.toContinuousLinearMap.lipschitzWith).add (LipschitzWith.const _))⟩

lemma XT_diff (z : ℝ) :
    ∀ᵐ g ∂normal m, HasFDerivAt (q.XT z)
      ((op (q.Pmat z g)).comp (op q.S)) g := by
  have hh := (coneProj_lip q.C).ae_differentiableAt (μ := volume)
  filter_upwards [(tendsto_ae_affineN q.root (q.shift z)).eventually hh] with g hg
  simp only [XT,Pmat,projJac_op]
  rw [← q.matrix_eq]
  have hl := hg.hasFDerivAt.comp g
    (q.root.hasFDerivAt.add_const (q.shift z))
  exact hl

lemma normal_XT_inner (z : ℝ) (u v : Rn m) :
    (∫ g, ⟪v,op (q.Pmat z g) (op q.S u)⟫ ∂normal m) =
    ∫ g, ⟪g,u⟫ * ⟪v,q.XT z g⟫ ∂normal m := by
  let l : Rn m →L[ℝ] ℝ := innerSL ℝ v
  obtain ⟨K,hK⟩ := q.XT_lipschitz z
  have he := normal_IBP_lipschitz (l.lipschitzWith.comp hK) u
  change _ = ∫ g, ⟪g,u⟫ • (l ∘ q.XT z) g ∂_
  rw [← he]
  apply integral_congr_ae
  filter_upwards [q.XT_diff z] with g hg
  rw [(l.hasFDerivAt.comp g hg).fderiv]
  rfl

lemma integrable_pair (z : ℝ) (u v : Rn m) :
    Integrable (fun g => ⟪g,u⟫ * ⟪v,q.XT z g⟫) (normal m) := by
  let l : Rn m →L[ℝ] ℝ := innerSL ℝ u
  let l' : Rn m →L[ℝ] ℝ := innerSL ℝ v
  have hi : Integrable (fun g => l g * l' (q.XT z g)) (normal m) := by
    apply PolyBound.gaussian_integrable
      ((PolyBound.clm l).mul ((PolyBound.clm l').comp (poly_sample ..)))
      ((l.continuous.mul (l'.continuous.comp (continuous_sample ..))).aestronglyMeasurable)
  convert hi using 1
  ext
  rw [real_inner_comm u]
  rfl

lemma integral_P_ip (z : ℝ) (x y : Rn m) :
    (∫ g, ⟪x,op (q.Pmat z g) y⟫ ∂normal m) =
      ⟪x,op (meanJac q.C q.root (q.shift z)) y⟫ :=
  (op_inner_integral (meanJac_integrable ..) _ _).symm

lemma trace_SPS (A : Mat m) :
    trace (q.covMat * A) = ∑ i, ⟪op q.S (std i),op A (op q.S (std i))⟫ := by
  change trace (q.S*q.S*A) = _
  rw [Matrix.mul_assoc,trace_mul_comm,trace_op]
  apply Finset.sum_congr rfl
  intro i _
  have H := op_iff_hermitian.mp q.pos.1 (std i) (op A (op q.S (std i)))
  simpa only [_root_.map_mul,mul_apply_eq_comp] using H.symm

theorem avH_as_mean_ip (z : ℝ) :
    q.avH z = (∫ g, ⟪q.XT z g,q.Z g⟫ ∂normal m) / (m:ℝ) := by
  unfold avH trN
  congr 1
  rw [q.trace_SPS]
  simp_rw [← q.integral_P_ip, q.normal_XT_inner]
  rw [← integral_finsetSum]
  · apply integral_congr_ae
    filter_upwards with g
    have he := (EuclideanSpace.basisFun (Fin m) ℝ).sum_repr' g
    have hu (i) : ⟪g,std i⟫ * ⟪op q.S (std i),q.XT z g⟫ =
        ⟪q.XT z g,op q.S (⟪std i,g⟫ • std i)⟫ := by
      rw [_root_.map_smul,real_inner_smul_right,real_inner_comm g,real_inner_comm (q.XT z g)]
    simp_rw [hu]
    rw [← inner_sum,← _root_.map_sum,he,q.Z_def]
  · exact fun i _ => q.integrable_pair z _ _

lemma avH_as_energy (z : ℝ) :
    q.avH z =
      (2 * meanEnergy q.C q.root (q.shift z) - ⟪q.shift z,a z • q.U⟫) / (m:ℝ) := by
  rw [q.avH_as_mean_ip]
  congr 1
  let x := q.shift z
  let l : Rn m →L[ℝ] ℝ := innerSL ℝ x
  have hh (g) : ⟪q.XT z g,q.Z g⟫ =
      2 * energy q.C (affineN q.root x g) - l (q.XT z g) := by
    have he := q.XP z g
    rw [q.YT_sub z g,inner_sub_right,inner_add_right,real_inner_self_eq_norm_sq] at he
    change _ = 2*(‖q.XT z g‖^2/2)- ⟪q.shift z,q.XT z g⟫
    rw [real_inner_comm (q.XT z g) (q.shift z)]
    linarith
  simp_rw [hh]
  have hi : Integrable (fun g => l (q.XT z g)) (normal m) :=
    l.integrable_comp (sample_integrable ..)
  rw [integral_sub ((energy_integrable ..).const_mul _) hi, integral_const_mul,
    l.integral_comp_comm (show Integrable (q.XT z) (normal m) from sample_integrable ..),
    q.XT_mean]
  rfl

lemma deriv_avH (z : ℝ) :
    HasDerivAt q.avH ((p z)*q.Bt z + (a z)*q.r1 z) z := by
  have hz := (q.shift_cd.differentiable (by norm_num)).differentiableAt (x := z) |>.hasDerivAt
  have he := (meanEnergy_derivative q.C q.root (q.shift z)).comp_hasDerivAt z hz
  have hh := (((he.const_mul (2:ℝ)).sub (hz.inner ℝ ((d_a z).smul_const q.U))).div_const (m:ℝ))
  rw [funext q.avH_as_energy]
  have hm : mean q.C q.root (q.shift z) = a z • q.U := q.XT_mean z
  convert hh using 1
  all_goals first
  | rfl
  | (rw [q.r1_eq,Bt,q.Y_mean,hm];
      simp only [inner_sub_right, innerSL_apply_apply,real_inner_smul_left,
        real_inner_smul_right]; simp only [real_inner_comm (q.U)]; ring)

section
variable [NeZero m]
-- the nonnegative variance correction in (6)
omit [NeZero m] in
lemma avH_variance (z : ℝ) :
    q.avH z = (∫ g, ‖q.XT z g-a z • q.U‖ ^ 2 ∂normal m)/(m:ℝ) +
      a z*q.Bt z := by
  let b := a z • q.U
  let l : Rn m →L[ℝ] ℝ := innerSL ℝ b
  have he : (fun g => ‖q.XT z g - a z • q.U‖^2) =
      fun g => 2*energy q.C (affineN q.root (q.shift z) g)-2*l (q.XT z g)+‖b‖^2 := by
    ext g
    change _ = 2*(‖q.XT z g‖^2/2)-2*⟪b,q.XT z g⟫+‖b‖^2
    rw [real_inner_comm]
    have hu := norm_sub_sq_real (q.XT z g) b
    change ‖q.XT z g-b‖^2 = _
    linarith
  have hi : Integrable (fun g => l (q.XT z g)) (normal m) :=
    l.integrable_comp (sample_integrable ..)
  rw [he]
  rw [integral_add, integral_sub, integral_const, integral_const_mul,integral_const_mul]
  · rw [l.integral_comp_comm (show Integrable (q.XT z) (normal m) from sample_integrable ..),
      q.XT_mean,q.avH_as_energy,Bt,q.Y_mean]
    simp only [probReal_univ,smul_eq_mul,one_mul]
    change _ = ( _*meanEnergy q.C q.root _ - _*⟪b,b⟫+_)/_+_
    rw [← real_inner_self_eq_norm_sq]
    dsimp only [b]
    simp only [inner_sub_right,real_inner_smul_left,real_inner_smul_right]
    rw [real_inner_comm (q.U)]
    ring
  all_goals
    first | exact (energy_integrable ..).const_mul _
          | exact hi.const_mul _
          | exact integrable_const _
          | exact ((energy_integrable ..).const_mul _).sub (hi.const_mul _)
end
end ProjField
end GeneralMahler

end

end OAI
