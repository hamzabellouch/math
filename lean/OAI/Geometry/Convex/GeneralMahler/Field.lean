import OAI.Geometry.Convex.GeneralMahler.CDF
import OAI.Geometry.Convex.GeneralMahler.Bias

namespace OAI
/-! §02, Gaussian field notation and mean equations. -/
noncomputable section
open MeasureTheory MeasureTheory.Measure Metric Filter Real Set Matrix
open scoped ENNReal NNReal Topology MatrixOrder Matrix.Norms.L2Operator RealInnerProductSpace
namespace GeneralMahler
open Layers

structure ProjField (m : ℕ) where
  C : ProperCone ℝ (Rn m)
  U : Rn m
  V : Rn m
  U_in : U ∈ interior (C : Set (Rn m))
  V_in : V ∈ interior (posDual C : Set (Rn m))
  ip : ⟪U,V⟫ = (m:ℝ)
  S : Mat m
  pos : S.PosDef
  root : Rn m ≃L[ℝ] Rn m
  matrix_eq : root.toContinuousLinearMap = op S

variable {m : ℕ}

namespace ProjField
variable (q : ProjField m)
abbrev D := posDual q.C
def covMat := q.S * q.S
def shift (z : ℝ) := bias q.C q.root (a z • q.U)
def XT (z : ℝ) := sample q.C q.root (q.shift z)
def Z (g : Rn m) := q.root g
def YT (z : ℝ) (g : Rn m) := coneProj q.D (-(q.Z g+q.shift z))
def Pmat (z : ℝ) (g : Rn m) := projJac q.C (q.Z g + q.shift z)

lemma Pmat_psd (z g) : 0 ≤ q.Pmat z g := (projJac_pos ..).nonneg
lemma Pmat_le (z g) : q.Pmat z g ≤ 1 := projJac_le_one ..
lemma Pmat_herm (z g) : (q.Pmat z g).IsHermitian := projJac_sym ..

lemma scaled_interior (z : ℝ) : a z • q.U ∈ interior (q.C:Set (Rn m)) := by
  have he : posDual q.D = q.C := ProperCone.innerDual_innerDual _
  rw [← he]
  obtain ⟨c,hc,h⟩ := interior_dual_bound (show q.U ∈ interior (posDual q.D:Set (Rn m))
    by rw [he]; exact q.U_in)
  apply interior_dual_of_bound (mul_pos (a_pos z) hc)
  intro x hx
  rw [real_inner_smul_left, mul_assoc]
  exact mul_le_mul_of_nonneg_left (h x hx) (a_pos z).le

lemma contDiff_a : ContDiff ℝ 1 Layers.a := contDiff_one_iff_deriv.mpr
    ⟨fun x => (d_a x).differentiableAt, by rw [show deriv a = p from funext fun x => (d_a x).deriv]; exact cp⟩

theorem shift_cd : ContDiff ℝ 1 q.shift := by
  rw [contDiff_iff_contDiffAt]
  intro z
  exact (bias_C_one q.C q.root _ (q.scaled_interior z)).comp z
    (contDiff_a.smul contDiff_const).contDiffAt

lemma XT_mean (z : ℝ) : ∫ x, q.XT z x ∂normal m = a z • q.U :=
  bias_mean q.C q.root _ (q.scaled_interior z)

lemma YT_sub (z x) : q.YT z x = q.XT z x - (q.Z x + q.shift z) :=
  proj_moreau q.C _

lemma Y_mean (z : ℝ) : ∫ x, q.YT z x ∂normal m = a z • q.U - q.shift z := by
  simp_rw [q.YT_sub]
  change ∫ x, sample q.C q.root (q.shift z) x-affineN q.root (q.shift z) x ∂normal m = _
  rw [integral_sub (sample_integrable ..) (affineN_integrable ..), affineN_mean]
  rw [← q.XT_mean z]; rfl

lemma XP (z x) : ⟪q.XT z x,q.YT z x⟫ = 0 := by
  rw [YT_sub]
  rw [real_inner_comm,show q.XT z x-(q.Z x+q.shift z) = -((q.Z x+q.shift z)-q.XT z x) by abel]
  rw [inner_neg_left]; exact neg_eq_zero.mpr (proj_orthogonal ..)

lemma deriv_shift_mean (z : ℝ) :
    op (meanJac q.C q.root (q.shift z)) (deriv q.shift z) = p z • q.U := by
  have hD := (q.shift_cd.differentiable (by norm_num)).differentiableAt (x := z) |>.hasDerivAt
  have he := (hasFDerivAt_mean q.C q.root _).comp_hasDerivAt z hD
  have hf : (mean q.C q.root) ∘ q.shift = fun z => a z • q.U := funext fun z => q.XT_mean z
  rw [hf] at he
  exact he.unique ((d_a z).smul_const _)

def Bt (z : ℝ) := (⟪q.U, ∫ g, q.YT z g ∂normal m⟫)/(m:ℝ)
def r1 (z : ℝ) := -deriv q.Bt z

lemma Bt_hasDeriv (z : ℝ) :
    HasDerivAt q.Bt (⟪q.U, p z • q.U-deriv q.shift z⟫/(m:ℝ)) z := by
  have hD := (q.shift_cd.differentiable (by norm_num)).differentiableAt (x := z) |>.hasDerivAt
  have hh : q.Bt = fun z => ⟪q.U,a z • q.U-q.shift z⟫/(m:ℝ) := funext fun z => by rw [Bt,Y_mean]
  rw [hh]
  have he := ((hasDerivAt_const z q.U).inner ℝ (((d_a z).smul_const q.U).sub hD)).div_const (m:ℝ)
  simpa only [inner_zero_left,zero_add,add_zero, Pi.sub_apply] using he

lemma r1_eq (z : ℝ) : q.r1 z = ⟪q.U,deriv q.shift z-p z • q.U⟫ / (m:ℝ) := by
  rw [r1,(q.Bt_hasDeriv z).deriv]
  simp only [inner_sub_right]; ring

lemma Bt_nonneg (z : ℝ) : 0 ≤ q.Bt z := by
  have he := affineN_integrable q.root (q.shift z)
  have hi : Integrable (q.YT z) (normal m) := by
    rw [funext (q.YT_sub z)]
    exact (sample_integrable ..).sub he
  unfold Bt
  apply div_nonneg _ (Nat.cast_nonneg m)
  change 0 ≤ (innerSL ℝ q.U) (∫ g, q.YT z g ∂_)
  rw [← (innerSL ℝ q.U).integral_comp_comm hi]
  exact integral_nonneg fun x => mem_posDual.mp (proj_mem ..) (interior_subset q.U_in)

section
variable [NeZero m]
lemma r1_pos (z : ℝ) : 0 < q.r1 z := by
  rw [q.r1_eq]
  have hp : 0 < (m:ℝ) := by exact_mod_cast (Nat.pos_of_ne_zero (NeZero.ne m))
  apply div_pos _ hp
  let A := meanJac q.C q.root (q.shift z)
  let b := deriv q.shift z
  have hu : q.U ≠ 0 := by
    intro h
    have he := q.ip
    rw [h,inner_zero_left] at he; linarith
  have hq : op A b = p z • q.U := q.deriv_shift_mean z
  let x := op A b
  have hx : x ≠ 0 := by
    change op A b ≠ _
    rw [hq]; exact smul_ne_zero (p_pos z).ne' hu
  have he : 0 < ⟪x,b-x⟫ := by
    have hpos := mean_pos q.C q.root ⟨_,q.U_in⟩ (q.shift z)
    have hless := mean_lt_one q.C q.root ⟨_,q.V_in⟩ (q.shift z)
    -- decompose b=x+y; evaluate ⟪x,y⟫ = A and I-A energies
    have h₁ := (op_posDef_iff.mp hless).2 x hx
    have h₂ : 0 ≤ ⟪b-x,op A (b-x)⟫ := (op_posSemidef_iff.mp hpos.posSemidef).2 _
    rw [_root_.map_sub,_root_.map_one,_root_.sub_apply] at h₁
    change 0 < ⟪x,x-op A x⟫ at h₁
    have hu := op_iff_hermitian.mp hpos.1 b x
    change ⟪op A b,x⟫ = ⟪b,op A x⟫ at hu
    rw [_root_.map_sub] at h₂
    change 0 ≤ ⟪b-x,x-op A x⟫ at h₂
    change ⟪x,x⟫ = ⟪b,op A x⟫ at hu
    simp only [inner_sub_left,inner_sub_right] at *
    rw [real_inner_comm b]
    linarith
  dsimp only [x] at he
  rw [hq,real_inner_smul_left] at he; exact pos_of_mul_pos_right he (p_pos z).le
end
end ProjField
end GeneralMahler

end

end OAI
