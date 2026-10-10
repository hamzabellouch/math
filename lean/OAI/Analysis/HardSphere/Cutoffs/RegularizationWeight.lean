import Mathlib
import OAI.Analysis.HardSphere.Geometry.HeatScalar
import OAI.Analysis.HardSphere.Orbitals.StrongContractionLimitDense

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
noncomputable section
open scoped BigOperators ComplexConjugate
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
noncomputable section
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
namespace HardSphere
open scoped Topology
open ContinuousLinearMap

def regularizationWeight (δ x : ℝ) : ℝ := (δ+(1-δ)*x)⁻¹

lemma regularization_denom_pos {δ x : ℝ} (hδ : 0<δ) (hx : x∈Set.Icc (0:ℝ) 1) :
    0<δ+(1-δ)*x := by
  have he : δ+(1-δ)*x=δ*(1-x)+x := by ring
  rw [he]
  by_cases h : x=0
  · simp [h,hδ]
  · exact add_pos_of_nonneg_of_pos (mul_nonneg hδ.le (sub_nonneg.mpr hx.2))
      (lt_of_le_of_ne hx.1 (Ne.symm h))

lemma regularization_weight_continuous {δ : ℝ} (hδ : 0<δ) :
    ContinuousOn (regularizationWeight δ) (Set.Icc (0:ℝ) 1) := by
  apply (continuous_const.add (continuous_const.mul continuous_id)).continuousOn.inv₀
  exact fun x hx ↦ ne_of_gt (regularization_denom_pos hδ hx)

lemma regularization_energy_bound {δ x : ℝ} (hδ : 0<δ) (hx : x∈Set.Icc (0:ℝ) 1) :
    x*(regularizationWeight δ x)^2 ≤ 1+δ⁻¹*(1-heatScalar δ x) := by
  by_cases hx0 : x=0
  · simp only [hx0,zero_mul,heatScalar_zero,sub_zero,mul_one]
    positivity
  have hxp : 0<x := lt_of_le_of_ne hx.1 (Ne.symm hx0)
  let e : ℝ := x⁻¹-1
  have he0 : 0≤e := by
    dsimp [e]
    exact sub_nonneg.mpr ((one_le_inv₀ hxp).mpr hx.2)
  have hd : 0<1+δ*e := by positivity
  have hexp : Real.exp (-δ*e)≤(1+δ*e)⁻¹ := by
    rw [neg_mul,Real.exp_neg]
    exact inv_anti₀ hd (by simpa [add_comm] using Real.add_one_le_exp (δ*e))
  have hh : heatScalar δ x=Real.exp (-δ*e) := by
    rw [heatScalar_of_pos hδ hxp]
    congr 1
    dsimp [e]
    field_simp
    ring
  have he : x*(regularizationWeight δ x)^2=(1+e)/(1+δ*e)^2 := by
    dsimp [regularizationWeight,e]
    field_simp
    ring
  rw [he,hh]
  have hden : 1≤1+δ*e := by linarith [mul_nonneg hδ.le he0]
  calc
    _ ≤ (1+e)/(1+δ*e) := div_le_div_of_nonneg_left (by positivity) hd (by nlinarith)
    _ ≤ 1+e/(1+δ*e) := by
      apply (div_le_iff₀ hd).mpr
      rw [add_mul,div_mul_cancel₀ _ hd.ne']
      nlinarith
    _ = 1+δ⁻¹*(1-(1+δ*e)⁻¹) := by field_simp; ring
    _ ≤ _ := add_le_add_right (mul_le_mul_of_nonneg_left (sub_le_sub_left hexp _) (inv_nonneg.mpr hδ.le)) _

section
variable {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
  [InnerProductSpace ℂ E] [InnerProductSpace ℂ F] [CompleteSpace E] [CompleteSpace F] [Nontrivial F]
local instance scalarOperatorRealAlgebraRegularizedLift : Algebra ℝ (F →L[ℂ] F) := Algebra.restrictScalars ℝ ℂ _

lemma positive_contraction_spectrum {R : F →L[ℂ] F} (hR : R.IsPositive) (hRn : ‖R‖≤1) :
    spectrum ℝ R⊆Set.Icc (0:ℝ) 1 := by
  intro x hx
  refine ⟨spectrum_nonneg_of_nonneg (ContinuousLinearMap.nonneg_iff_isPositive.mpr hR) hx,?_⟩
  have hb : |x|≤‖R‖ := by simpa only [Real.norm_eq_abs] using spectrum.norm_le_norm_of_mem hx
  exact (le_abs_self x).trans (hb.trans hRn)

lemma regularized_lift_norm_sq (A : E →L[ℂ] F) (hA : ‖A‖≤1) {δ : ℝ}
    (hδ : 0<δ) (f : F) :
    let R := A.comp A.adjoint
    let W := cfc (p := IsSelfAdjoint) (regularizationWeight δ) R
    ‖A.adjoint (W f)‖^2 ≤
      ‖f‖^2+δ⁻¹*(‖f‖^2-(inner ℂ f ((cfc (p := IsSelfAdjoint) (heatScalar δ) R) f)).re) := by
  intro R W
  have hRp : R.IsPositive := by
    simpa [R] using isPositive_adjoint_comp_self A.adjoint
  have hRn : ‖R‖≤1 := by
    exact (opNorm_comp_le _ _).trans (by rw [adjoint.norm_map]; nlinarith [norm_nonneg A])
  have hspec := positive_contraction_spectrum hRp hRn
  have hw := (regularization_weight_continuous hδ).mono hspec
  have hW : IsSelfAdjoint W := IsSelfAdjoint.cfc
  have hnorm : ‖A.adjoint (W f)‖^2 = (inner ℂ f
      ((cfc (p := IsSelfAdjoint) (fun x ↦ x*(regularizationWeight δ x)^2) R) f)).re := by
    rw [norm_sq_eq_re_inner (𝕜 := ℂ)]
    have he : cfc (p := IsSelfAdjoint) (fun x ↦ x*(regularizationWeight δ x)^2) R = W*R*W := by
      calc
        _ = cfc (p := IsSelfAdjoint) (fun x ↦ regularizationWeight δ x*x*regularizationWeight δ x) R := by
          congr 1
          funext x
          ring
        _ = _ := by
          rw [cfc_mul (fun x:ℝ ↦ regularizationWeight δ x*x) (regularizationWeight δ) R (hw.mul continuous_id.continuousOn) hw,
            cfc_mul (regularizationWeight δ) (fun x:ℝ ↦ x) R hw continuous_id.continuousOn,cfc_id' ℝ R hRp.isSelfAdjoint]
    rw [he,mul_apply_eq_comp,mul_apply_eq_comp]
    change (inner ℂ (A.adjoint (W f)) (A.adjoint (W f))).re = _
    rw [adjoint_inner_left]
    change (inner ℂ (W f) (R (W f))).re = _
    rw [← adjoint_inner_right W f (R (W f)),hW.adjoint_eq]
  have hle : cfc (p := IsSelfAdjoint) (fun x ↦ x*(regularizationWeight δ x)^2) R ≤
      cfc (p := IsSelfAdjoint) (fun x ↦ 1+δ⁻¹*(1-heatScalar δ x)) R :=
    cfc_mono (fun x hx ↦ regularization_energy_bound hδ (hspec hx))
      (continuous_id.continuousOn.mul (hw.pow 2))
      (continuousOn_const.add (continuousOn_const.mul
        (continuousOn_const.sub (heatScalar_smooth δ).continuous.continuousOn)))
  have hp := ContinuousLinearMap.le_def.mp hle |>.re_inner_nonneg_right f
  have heval : cfc (p := IsSelfAdjoint) (fun x ↦ 1+δ⁻¹*(1-heatScalar δ x)) R =
      1+δ⁻¹ • (1-cfc (p := IsSelfAdjoint) (heatScalar δ) R) := by
    have hh := (heatScalar_smooth δ).continuous.continuousOn (s := spectrum ℝ R)
    rw [cfc_add (a := R) (fun _ : ℝ ↦ 1) (fun x:ℝ ↦ δ⁻¹*(1-heatScalar δ x)) continuousOn_const (continuousOn_const.mul (continuousOn_const.sub hh)),
      cfc_mul (fun _ : ℝ ↦ δ⁻¹) (fun x:ℝ ↦ 1-heatScalar δ x) R continuousOn_const (continuousOn_const.sub hh),
      cfc_sub (fun _ : ℝ ↦ 1) (heatScalar δ) R continuousOn_const hh,
      cfc_const 1 R hRp.isSelfAdjoint,cfc_const δ⁻¹ R hRp.isSelfAdjoint]
    simp only [Algebra.algebraMap_eq_smul_one,one_smul,smul_mul_assoc,one_mul]
  change 0≤(inner ℂ f ((cfc (p := IsSelfAdjoint) (fun x ↦ 1+δ⁻¹*(1-heatScalar δ x)) R-
    cfc (p := IsSelfAdjoint) (fun x ↦ x*(regularizationWeight δ x)^2) R) f)).re at hp
  rw [sub_apply,inner_sub_right,Complex.sub_re,heval,add_apply,smul_apply,sub_apply,
    one_apply_eq_self,inner_add_right,Complex.add_re] at hp
  have hself : (inner ℂ f f).re=‖f‖^2 := (norm_sq_eq_re_inner (𝕜 := ℂ) f).symm
  have hi : (inner ℂ f (δ⁻¹ • (f-(cfc (p := IsSelfAdjoint) (heatScalar δ) R) f))).re =
      δ⁻¹*(‖f‖^2-(inner ℂ f ((cfc (p := IsSelfAdjoint) (heatScalar δ) R) f)).re) := by
    rw [RCLike.real_smul_eq_coe_smul (K := ℂ),inner_smul_real_right,inner_sub_right,Complex.real_smul,Complex.mul_re,Complex.sub_re]
    simp only [Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero,hself]
  rw [hi,hself,← hnorm] at hp
  linarith
end
end HardSphere

namespace HardSphere
open ContinuousLinearMap Filter
open scoped Topology

lemma regularization_scalar_mem {δ x : ℝ} (hδ : 0<δ) (hx : x∈Set.Icc (0:ℝ) 1) :
    x*regularizationWeight δ x∈Set.Icc (0:ℝ) 1 := by
  have hd := regularization_denom_pos hδ hx
  change 0≤x*(δ+(1-δ)*x)⁻¹ ∧ x*(δ+(1-δ)*x)⁻¹≤1
  rw [← div_eq_mul_inv,div_le_one hd]
  exact ⟨div_nonneg hx.1 hd.le,by nlinarith [mul_nonneg hδ.le (sub_nonneg.mpr hx.2)]⟩

lemma regularization_error_bound {δ x : ℝ} (hδ : 0<δ) (hx : x∈Set.Icc (0:ℝ) 1) :
    |(x*regularizationWeight δ x-1)*x|≤δ := by
  have hs := regularization_scalar_mem hδ hx
  have he : (x*regularizationWeight δ x-1)*x = -δ*(1-x)*(x*regularizationWeight δ x) := by
    have hd := regularization_denom_pos hδ hx
    dsimp [regularizationWeight]
    have hi : (δ+(1-δ)*x)*(δ+(1-δ)*x)⁻¹=1 := mul_inv_cancel₀ hd.ne'
    nlinarith only [congrArg (fun y:ℝ ↦ y*x) hi]
  rw [he,abs_mul,abs_mul,abs_neg,abs_of_pos hδ,abs_of_nonneg (sub_nonneg.mpr hx.2),abs_of_nonneg hs.1]
  calc
    _ ≤ δ*1*1 := mul_le_mul (mul_le_mul_of_nonneg_left (by linarith [hx.1] : 1-x≤1) hδ.le)
      hs.2 hs.1 (by positivity)
    _ = δ := by ring

section
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [CompleteSpace F] [Nontrivial F]
local instance : Algebra ℝ (F →L[ℂ] F) := Algebra.restrictScalars ℝ ℂ _

def regularizationOperator (R : F →L[ℂ] F) (δ : ℝ) : F →L[ℂ] F :=
  cfc (p := IsSelfAdjoint) (fun x ↦ x*regularizationWeight δ x) R

lemma regularizationOperator_norm_le {R : F →L[ℂ] F} (hRp : R.IsPositive) (hRn : ‖R‖≤1)
    {δ : ℝ} (hδ : 0<δ) : ‖regularizationOperator R δ‖≤1 := by
  apply norm_cfc_le zero_le_one
  intro x hx
  have hs := regularization_scalar_mem hδ (positive_contraction_spectrum hRp hRn hx)
  simpa only [Real.norm_eq_abs,abs_of_nonneg hs.1] using hs.2

lemma regularizationOperator_eq {R : F →L[ℂ] F} (hRp : R.IsPositive) (hRn : ‖R‖≤1)
    {δ : ℝ} (hδ : 0<δ) :
    regularizationOperator R δ = R*cfc (p := IsSelfAdjoint) (regularizationWeight δ) R := by
  rw [regularizationOperator,cfc_mul (fun x:ℝ ↦ x) (regularizationWeight δ) R
    continuous_id.continuousOn ((regularization_weight_continuous hδ).mono
      (positive_contraction_spectrum hRp hRn)),cfc_id' ℝ R hRp.isSelfAdjoint]

lemma regularizationOperator_range_error {R : F →L[ℂ] F} (hRp : R.IsPositive) (hRn : ‖R‖≤1)
    {δ : ℝ} (hδ : 0<δ) : ‖(regularizationOperator R δ-1)*R‖≤δ := by
  have hw := (regularization_weight_continuous hδ).mono (positive_contraction_spectrum hRp hRn)
  have he : (regularizationOperator R δ-1)*R =
      cfc (p := IsSelfAdjoint) (fun x ↦ (x*regularizationWeight δ x-1)*x) R := by
    rw [cfc_mul (fun x:ℝ ↦ x*regularizationWeight δ x-1) (fun x:ℝ ↦ x) R
      ((continuous_id.continuousOn.mul hw).sub continuousOn_const) continuous_id.continuousOn,
      cfc_sub (fun x:ℝ ↦ x*regularizationWeight δ x) (fun _:ℝ ↦ 1) R
        (continuous_id.continuousOn.mul hw) continuousOn_const,
      cfc_const 1 R hRp.isSelfAdjoint,cfc_id' ℝ R hRp.isSelfAdjoint]
    simp only [map_one,regularizationOperator]
  rw [he]
  exact norm_cfc_le hδ.le (fun x hx ↦ by
    simpa only [Real.norm_eq_abs] using regularization_error_bound hδ (positive_contraction_spectrum hRp hRn hx))

lemma regularizationOperator_tendsto {ι : Type*} {l : Filter ι} {d : ι→ℝ}
    (hd : ∀ i, 0<d i) (ht : Tendsto d l (𝓝 0))
    {R : F →L[ℂ] F} (hRp : R.IsPositive) (hRn : ‖R‖≤1) (hRd : DenseRange R) (f : F) :
    Tendsto (fun i ↦ regularizationOperator R (d i) f) l (𝓝 f) := by
  have hC (i : ι) (u : F) : ‖regularizationOperator R (d i) u‖≤‖u‖ := by
    exact (le_opNorm _ _).trans (by simpa only [one_mul] using
      (mul_le_mul_of_nonneg_right (regularizationOperator_norm_le hRp hRn (hd i)) (norm_nonneg u)))
  have hRange : ∀ u : F, Tendsto (fun i ↦ regularizationOperator R (d i) (R u)) l (𝓝 (R u)) := by
    intro u
    rw [← tendsto_sub_nhds_zero_iff, tendsto_zero_iff_norm_tendsto_zero]
    apply squeeze_zero' (g := fun i ↦ d i*‖u‖) (Eventually.of_forall fun _ ↦ norm_nonneg _) ?_ ?_
    · exact Eventually.of_forall fun i ↦ by
        change ‖((regularizationOperator R (d i)-1)*R) u‖≤_
        exact (le_opNorm _ _).trans (mul_le_mul_of_nonneg_right
          (regularizationOperator_range_error hRp hRn (hd i)) (norm_nonneg u))
    · simpa using ht.mul_const ‖u‖
  have h := strong_contraction_limit_of_dense (fun i ↦ regularizationOperator R (d i))
    (ContinuousLinearMap.id ℂ F) hC (by simp) R hRd hRange f
  exact h

end
end HardSphere

end
end
end
end
end
end

end OAI
