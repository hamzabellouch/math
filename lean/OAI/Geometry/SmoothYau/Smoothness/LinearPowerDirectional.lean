import Mathlib

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter Metric
open scoped Topology InnerProductSpace
open Set Filter Function Metric
open scoped Topology
open Set Filter Function Metric
open scoped Topology
open Set Filter Function Manifold
open scoped Topology ContDiff InnerProductSpace
section StereoJets
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma stereoAux_directional (v x w : E) :
    fderiv ℝ (stereoInvFunAux v) x w =
      (‖x‖^2+4)⁻¹ • ((4:ℝ) • w + (2 * inner ℝ x w) • v) -
      ((‖x‖^2+4)⁻¹ ^2 * (2 * inner ℝ x w)) •
        ((4:ℝ) • x + (‖x‖^2-4) • v) := by
  have hn : HasFDerivAt (fun y : E => ‖y‖^2) ((2:ℝ) • innerSL ℝ x) x := by
    simpa only [two_smul] using (hasStrictFDerivAt_norm_sq x).hasFDerivAt
  have hi := (hasFDerivAt_inv (by positivity : ‖x‖^2+4 ≠ 0)).comp x (hn.add_const 4)
  have hp := ((hasFDerivAt_id x).const_smul (4:ℝ)).add ((hn.sub_const 4).smul_const v)
  have hh := hi.smul hp
  change HasFDerivAt (stereoInvFunAux v) _ x at hh
  rw [hh.fderiv]
  simp only [_root_.add_apply,_root_.smul_apply,
    ContinuousLinearMap.smulRight_apply,ContinuousLinearMap.id_apply,innerSL_apply_apply,
    smul_eq_mul]
  simp [Function.comp_apply,ContinuousLinearMap.comp_apply,smul_add,smul_smul,inv_pow,sub_eq_add_neg]
  module

theorem stereoAux_second_jet (v w : E) :
    HasFDerivAt (fun x : E => fderiv ℝ (stereoInvFunAux v) x w)
      ((innerSL ℝ w).smulRight v) 0 := by
  have hn : HasFDerivAt (fun y : E => ‖y‖^2) (0 : E →L[ℝ] ℝ) 0 := by
    convert (hasStrictFDerivAt_norm_sq (0:E)).hasFDerivAt using 1
    simp
  have hi := (hasFDerivAt_inv (by norm_num : ‖(0:E)‖^2+4 ≠ 0)).comp (0:E) (hn.add_const 4)
  have ht := ((innerSL ℝ w).hasFDerivAt (x := (0:E))).const_mul 2
  have ht' : HasFDerivAt (fun x : E => 2 * inner ℝ x w) ((2:ℝ) • innerSL ℝ w) 0 := by
    simpa only [innerSL_apply_apply,real_inner_comm] using ht
  have hp := ((hasFDerivAt_id (0:E)).const_smul (4:ℝ)).add ((hn.sub_const 4).smul_const v)
  have hq := hi.smul ((hasFDerivAt_const ((4:ℝ) • w) (0:E)).add (ht'.smul_const v))
  have hr := ((hi.pow 2).mul ht').smul hp
  convert hq.sub hr using 1
  · funext x
    exact stereoAux_directional v x w
  · ext z
    simp only [norm_zero,zero_pow (by norm_num : (2:ℕ) ≠ 0),zero_add,
      inner_zero_left,innerSL_apply_apply,_root_.add_apply,
      _root_.sub_apply,_root_.smul_apply,
      ContinuousLinearMap.smulRight_apply,_root_.zero_apply,
      ContinuousLinearMap.id_apply,smul_eq_mul ]
    norm_num [smul_add,smul_smul]
    module
end StereoJets
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

def roundChart (p : E) (L : F →ₗᵢ[ℝ] E) (x : F) : E := stereoInvFunAux (-p) (L x)

lemma roundChart_smooth (p : E) (L : F →ₗᵢ[ℝ] E) : ContDiff ℝ ∞ (roundChart p L) :=
  contDiff_stereoInvFunAux.comp L.contDiff

lemma roundChart_zero (p : E) (L : F →ₗᵢ[ℝ] E) : roundChart p L 0 = p := by
  simp [roundChart,stereoInvFunAux]

lemma roundChart_first (p : E) (L : F →ₗᵢ[ℝ] E) :
    HasFDerivAt (roundChart p L) L.toContinuousLinearMap 0 := by
  have h : HasFDerivAt (stereoInvFunAux (-p)) (ContinuousLinearMap.id ℝ E)
      (L.toContinuousLinearMap 0) := by simpa using hasFDerivAt_stereoInvFunAux (-p)
  convert h.comp (0:F) L.toContinuousLinearMap.hasFDerivAt using 1
  · rfl
  · ext z
    rfl

lemma roundChart_directional (p : E) (L : F →ₗᵢ[ℝ] E) (x w : F) :
    fderiv ℝ (roundChart p L) x w = fderiv ℝ (stereoInvFunAux (-p)) (L x) (L w) := by
  rw [show roundChart p L = stereoInvFunAux (-p) ∘ L.toContinuousLinearMap from rfl,
    fderiv_comp x ((contDiff_stereoInvFunAux (m := ∞)).differentiable (by simp)).differentiableAt
      L.toContinuousLinearMap.differentiableAt]
  rw [ContinuousLinearMap.fderiv]
  rfl

lemma roundChart_second (p : E) (L : F →ₗᵢ[ℝ] E) (w : F) :
    HasFDerivAt (fun x => fderiv ℝ (roundChart p L) x w)
      ((innerSL ℝ w).smulRight (-p)) 0 := by
  have h : HasFDerivAt (fun x : E => fderiv ℝ (stereoInvFunAux (-p)) x (L w))
      ((innerSL ℝ (L w)).smulRight (-p)) (L.toContinuousLinearMap 0) := by
    simpa using stereoAux_second_jet (-p) (L w)
  have hh := h.comp (0:F) L.toContinuousLinearMap.hasFDerivAt
  convert hh using 1
  · funext x
    exact roundChart_directional p L x w
  · ext z
    simp

theorem roundChart_metric_first (p : E) (L : F →ₗᵢ[ℝ] E)
    (hL : ∀ w, inner ℝ p (L w) = 0) (v w : F) :
    HasFDerivAt (fun x => inner ℝ (fderiv ℝ (roundChart p L) x v)
      (fderiv ℝ (roundChart p L) x w)) (0 : F →L[ℝ] ℝ) 0 := by
  have hL' : ∀ z, inner ℝ (L z) p = 0 := fun z => (real_inner_comm _ _).trans (hL z)
  have hh := (roundChart_second p L v).inner ℝ (roundChart_second p L w)
  convert! hh using 1
  ext z
  simp [fderivInnerCLM_apply, (roundChart_first p L).fderiv,
    ContinuousLinearMap.smulRight_apply,inner_smul_left,inner_smul_right,hL,hL']


end

open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter Metric
open scoped Topology InnerProductSpace
open Set Filter Function Metric
open scoped Topology
open Set Filter Function Metric
open scoped Topology
open Set Filter Manifold
open scoped Topology ContDiff
open Set Filter MeasureTheory Metric
open scoped Topology ENNReal NNReal
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter Metric
open scoped Topology InnerProductSpace
open Set Filter Function Metric
open scoped Topology
open Set Filter Function Metric
open scoped Topology
open Set Filter Function
open scoped ContDiff InnerProductSpace Topology
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

lemma linearPower_directional (ℓ : E →L[ℝ] ℂ) (n : ℕ) (x w : E) :
    fderiv ℝ (fun y => (ℓ y)^n) x w = (n:ℂ) * (ℓ x)^(n-1) * ℓ w := by
  rw [(ℓ.hasFDerivAt.pow n).fderiv]
  simp [smul_eq_mul,mul_assoc]

lemma roundLinearPower_directional (ℓ : E →L[ℝ] ℂ) (n : ℕ) (p : E)
    (L : F →ₗᵢ[ℝ] E) (x w : F) :
    fderiv ℝ (fun y => (ℓ (roundChart p L y))^n) x w =
      (n:ℂ) * (ℓ (roundChart p L x))^(n-1) * ℓ (fderiv ℝ (roundChart p L) x w) := by
  have hc := ((roundChart_smooth p L).differentiable (by simp) x).hasFDerivAt
  have hh := (ℓ.hasFDerivAt.comp x hc).pow n
  convert! congrArg (fun D => D w) hh.fderiv using 1
  simp [smul_eq_mul,mul_assoc]

lemma roundLinearPower_second (ℓ : E →L[ℝ] ℂ) (n : ℕ) (p : E)
    (L : F →ₗᵢ[ℝ] E) (v w : F) :
    fderiv ℝ (fun y => fderiv ℝ (fun z => (ℓ (roundChart p L z))^n) y w) 0 v =
      (n:ℂ) * ((n-1:ℕ):ℂ) * (ℓ p)^(n-2) * ℓ (L v) * ℓ (L w) -
        (n:ℂ) * (ℓ p)^(n-1) * ℓ p * (inner ℝ w v : ℂ) := by
  have ha := (ℓ.hasFDerivAt.comp (0:F) (roundChart_first p L)).pow (n-1)
  have hb := ℓ.hasFDerivAt.comp (0:F) (roundChart_second p L w)
  have hh := (ha.const_mul (n:ℂ)).mul hb
  have he : (fun y => fderiv ℝ (fun z => (ℓ (roundChart p L z))^n) y w) =
      (fun y => (n:ℂ) * (ℓ (roundChart p L y))^(n-1)) *
        (fun y => ℓ (fderiv ℝ (roundChart p L) y w)) := by
    funext y
    exact roundLinearPower_directional ℓ n p L y w
  simp only [Function.comp_def] at hh
  rw [he]
  convert! congrArg (fun D => D v) hh.fderiv using 1
  simp [roundChart_zero,(roundChart_first p L).fderiv,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.smulRight_apply,innerSL_apply_apply,_root_.smul_apply,
    smul_eq_mul,show n-1-1=n-2 by omega]
  ring

lemma roundLinearPower_second_of_two_le (ℓ : E →L[ℝ] ℂ) (n : ℕ) (hn : 2 ≤ n) (p : E)
    (L : F →ₗᵢ[ℝ] E) (v w : F) :
    fderiv ℝ (fun y => fderiv ℝ (fun z => (ℓ (roundChart p L z))^n) y w) 0 v =
      (n:ℂ) * ((n:ℂ)-1) * (ℓ p)^(n-2) * ℓ (L v) * ℓ (L w) -
        (n:ℂ) * (ℓ p)^n * (inner ℝ w v : ℂ) := by
  rw [roundLinearPower_second]
  have h1 : ((n-1:ℕ):ℂ) = (n:ℂ)-1 := by rw [Nat.cast_sub (by omega),Nat.cast_one]
  have h2 : (ℓ p)^(n-1) * ℓ p = (ℓ p)^n := by
    rw [← pow_succ, Nat.sub_add_cancel (by omega)]
  rw [h1]
  rw [mul_assoc (n:ℂ) ((ℓ p)^(n-1)),h2]
lemma fderiv_real_part {f : F → ℂ} {x : F} (hf : DifferentiableAt ℝ f x) (v : F) :
    fderiv ℝ (fun y => (f y).re) x v = (fderiv ℝ f x v).re := by
  have hh := Complex.reCLM.hasFDerivAt.comp x hf.hasFDerivAt
  convert! congrArg (fun D => D v) hh.fderiv using 1

lemma second_real_part {f : F → ℂ} (hf : ContDiff ℝ ∞ f) (x v w : F) :
    fderiv ℝ (fun y => fderiv ℝ (fun z => (f z).re) y w) x v =
      (fderiv ℝ (fun y => fderiv ℝ f y w) x v).re := by
  simp_rw [fderiv_real_part (hf.differentiable (by simp) _)]
  apply fderiv_real_part
  exact (((hf.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const).differentiable (by simp)) x

lemma roundLinearPower_real_second (ℓ : E →L[ℝ] ℂ) (n : ℕ) (hn : 2 ≤ n) (p : E)
    (L : F →ₗᵢ[ℝ] E) (v w : F) :
    fderiv ℝ (fun y => fderiv ℝ (fun z => ((ℓ (roundChart p L z))^n).re) y w) 0 v =
      ((n:ℂ) * ((n:ℂ)-1) * (ℓ p)^(n-2) * ℓ (L v) * ℓ (L w) -
        (n:ℂ) * (ℓ p)^n * (inner ℝ w v : ℂ)).re := by
  have hf : ContDiff ℝ ∞ (fun z => (ℓ (roundChart p L z))^n) :=
    (ℓ.contDiff.comp (roundChart_smooth p L)).pow n
  rw [second_real_part hf,roundLinearPower_second_of_two_le ℓ n hn]




end YauCounterexamples
end

end OAI
