import Mathlib
import OAI.Geometry.SmoothYau.SphereMetric.ThreeFormulaNormedSpace
import OAI.Geometry.SmoothYau.SphereMetric.ThreeRobustProfileNormedSpace

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set Filter Function Manifold Module
open scoped Topology ContDiff InnerProductSpace Matrix
local instance threeValueNormedSpace : NormedSpace ℝ ThreeModel := inferInstance
local instance threeValueContinuousSMul : ContinuousSMul ℝ ThreeModel := IsBoundedSMul.continuousSMul
local instance threeValue_dimension_fact (n : ℕ) : Fact (Module.finrank ℝ (Euclidean (n+1))=n+1) := ⟨by simp [Euclidean]⟩
lemma threeCoupled_gradient_value (r : ℝ) (k : ℕ) (hk : 1 ≤ k) (p : ThreeManifold) :
    coordinateGradientPair threeBackgroundMetric (threeCoupled r k) (threeCoupled r k) p=
      (k:ℝ)^2*((( (p.2:ℂ)^k*productA p.1^(k-1)).re+
        ((p.2:ℂ)^k*(r:ℂ)^k*productB p.1^(k-1)).re)^2+
        ((p.2:ℂ)^k*productA p.1^(k-1)).im^2+
        ((p.2:ℂ)^k*(r:ℂ)^k*productB p.1^(k-1)).im^2-
        (threeCoupled r k p)^2+(threeCoupledComplex r k p).im^2) := by
  rw [three_gradient_pair_of_ambient_derivative p _ _ _ (threeCoupled_ambient_derivative r k hk p)]
  let α := (p.2:ℂ)^k*productA p.1^(k-1)
  let β := (p.2:ℂ)^k*(r:ℂ)^k*productB p.1^(k-1)
  have hp (z : ℂ) : z^(k-1)*z=z^k := by rw [←pow_succ,Nat.sub_add_cancel hk]
  have he : α*productA p.1+β*productB p.1=threeCoupledComplex r k p := by
    dsimp only [α,β,threeCoupledComplex]
    rw [←hp (productA p.1),←hp (productB p.1)]
    ring
  have haxis (i : Fin 3) : inner ℝ (p.1:Euclidean 3) (productAxis i)=(p.1:Euclidean 3) i := by
    rw [real_inner_comm,productAxis_coord]
  have hrad : inner ℝ (p.1:Euclidean 3) (threeAmbientSphereGradient r k p)=(k:ℝ)*threeCoupled r k p := by
    change inner ℝ (p.1:Euclidean 3) ((k:ℝ) • ((α.re+β.re) • productAxis 0-
      α.im • productAxis 1-β.im • productAxis 2))=(k:ℝ)*(threeCoupledComplex r k p).re
    rw [←he]
    simp only [inner_smul_right,inner_sub_right,haxis,Complex.add_re,Complex.mul_re,
      productA_re,productA_im,productB_re,productB_im]
    ring
  have hn : inner ℝ (Complex.I*(p.2:ℂ)) (Complex.I*(p.2:ℂ))=1 := by
    rw [real_inner_self_eq_norm_sq,norm_mul,Complex.norm_I,p.2.norm_coe]
    norm_num
  have ho : inner ℝ (p.2:ℂ) (Complex.I*(p.2:ℂ))=0 := by
    simp only [Complex.inner,Complex.mul_re,Complex.mul_im,Complex.I_re,Complex.I_im,
      Complex.conj_re,Complex.conj_im]
    ring
  rw [hrad]
  change inner ℝ ((k:ℝ) • ((α.re+β.re) • productAxis 0-α.im • productAxis 1-β.im • productAxis 2))
      ((k:ℝ) • ((α.re+β.re) • productAxis 0-α.im • productAxis 1-β.im • productAxis 2))-
      ((k:ℝ)*threeCoupled r k p)^2+
      (inner ℝ ((-(k:ℝ)*(threeCoupledComplex r k p).im) • (Complex.I*(p.2:ℂ)))
        ((-(k:ℝ)*(threeCoupledComplex r k p).im) • (Complex.I*(p.2:ℂ)))-
      (inner ℝ (p.2:ℂ) ((-(k:ℝ)*(threeCoupledComplex r k p).im) • (Complex.I*(p.2:ℂ))))^2)=_
  change _ = (k:ℝ)^2*((α.re+β.re)^2+α.im^2+β.im^2-
    (threeCoupled r k p)^2+(threeCoupledComplex r k p).im^2)
  simp only [inner_smul_left,inner_smul_right,inner_sub_left,inner_sub_right,
    productAxis_inner,hn,ho]
  norm_num [Fin.ext_iff]
  ring
end


section
open Set Filter Function Manifold Module Metric
open scoped Topology ContDiff InnerProductSpace Matrix
local instance threeCleanNormedSpace : NormedSpace ℝ ThreeModel := inferInstance
local instance threeCleanContinuousSMul : ContinuousSMul ℝ ThreeModel := IsBoundedSMul.continuousSMul
lemma complex_re_sq_le_norm_sq (z : ℂ) : z.re^2 ≤ ‖z‖^2 := by
  have hn := Complex.normSq_eq_norm_sq z
  simp only [Complex.normSq_apply] at hn
  nlinarith [sq_nonneg z.im]
lemma complex_clean_energy_lower (C D A B : ℂ) (hA : ‖A‖ ≤ 3/4) (hB : ‖B‖ ≤ 1)
    (hD : ‖D‖ ≤ ‖C‖/100) (s : ℝ) :
    (1/32:ℝ)*‖C‖^2 ≤ (C.re+D.re)^2+C.im^2+D.im^2-(C*A+D*B).re^2+s^2 := by
  have hC := Complex.normSq_eq_norm_sq C
  have hDq := Complex.normSq_eq_norm_sq D
  simp only [Complex.normSq_apply] at hC hDq
  have hAs : ‖A‖^2≤(3/4:ℝ)^2 := sq_le_sq₀ (norm_nonneg _) (by norm_num) |>.mpr hA
  have hBs : ‖B‖^2≤1 := by nlinarith [norm_nonneg B]
  have hDs : ‖D‖^2≤‖C‖^2/10000 := by
    have hh := (sq_le_sq₀ (norm_nonneg D) (by positivity : 0≤‖C‖/100)).mpr hD
    nlinarith
  have hCA := complex_re_sq_le_norm_sq (C*A)
  have hDB := complex_re_sq_le_norm_sq (D*B)
  rw [norm_mul,mul_pow] at hCA hDB
  have hCA' : (C*A).re^2≤(9/16:ℝ)*‖C‖^2 := by
    nlinarith [mul_le_mul_of_nonneg_left hAs (sq_nonneg ‖C‖)]
  have hDB' : (D*B).re^2≤‖D‖^2 := by
    nlinarith [mul_le_mul_of_nonneg_left hBs (sq_nonneg ‖D‖)]
  have hc : (C.re+D.re)^2+C.im^2+D.im^2≥(3/4:ℝ)*‖C‖^2-3*‖D‖^2 := by
    nlinarith [sq_nonneg (C.re/2+2*D.re),sq_nonneg C.im,sq_nonneg D.im]
  have hu : (C*A+D*B).re^2≤(45/64:ℝ)*‖C‖^2+5*‖D‖^2 := by
    rw [Complex.add_re]
    nlinarith [sq_nonneg ((C*A).re/2-2*(D*B).re)]
  nlinarith [sq_nonneg s,sq_nonneg ‖C‖]
lemma threeCoupled_clean_gradient_lower (k : ℕ) (hk : 1 ≤ k) (p : ThreeManifold)
    (hρ : 1/2 ≤ ‖productA p.1‖) (hρu : ‖productA p.1‖ ≤ 3/4) :
    (1/32:ℝ)*((k:ℝ)*‖productA p.1‖^k)^2 ≤
      coordinateGradientPair threeBackgroundMetric (threeCoupled threeCouplingRadius k)
        (threeCoupled threeCouplingRadius k) p := by
  let C := (p.2:ℂ)^k*productA p.1^(k-1)
  let D := (p.2:ℂ)^k*(threeCouplingRadius:ℂ)^k*productB p.1^(k-1)
  have hCn : ‖C‖=‖productA p.1‖^(k-1) := by simp [C,norm_pow]
  have hDn : ‖D‖≤‖C‖/100 := by
    have hr : 0≤threeCouplingRadius := by norm_num [threeCouplingRadius]
    have hrρ : threeCouplingRadius≤‖productA p.1‖ := by norm_num [threeCouplingRadius] at *; linarith
    have hB := pow_le_pow_left₀ (norm_nonneg (productB p.1)) (productB_norm_le p.1) (k-1)
    rw [one_pow] at hB
    have hDr : ‖D‖≤threeCouplingRadius^k := by
      simp only [D,norm_mul,norm_pow,Circle.norm_coe,one_pow,one_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hr]
      exact mul_le_of_le_one_right (pow_nonneg hr _) hB
    calc
      _ ≤ threeCouplingRadius^k := hDr
      _ = threeCouplingRadius*threeCouplingRadius^(k-1) := by rw [←pow_succ',Nat.sub_add_cancel hk]
      _ ≤ threeCouplingRadius*‖productA p.1‖^(k-1) := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hr hrρ _) hr
      _ = ‖C‖/100 := by rw [hCn]; norm_num [threeCouplingRadius]; ring
  have hp (z : ℂ) : z^(k-1)*z=z^k := by rw [←pow_succ,Nat.sub_add_cancel hk]
  have he : C*productA p.1+D*productB p.1=threeCoupledComplex threeCouplingRadius k p := by
    dsimp only [C,D,threeCoupledComplex]
    rw [←hp (productA p.1),←hp (productB p.1)]
    ring
  have hl := complex_clean_energy_lower C D (productA p.1) (productB p.1) hρu (productB_norm_le p.1) hDn
    (threeCoupledComplex threeCouplingRadius k p).im
  rw [he] at hl
  have hstep : ‖productA p.1‖^k ≤ ‖C‖ := by
    rw [hCn,show k=(k-1)+1 by omega,pow_succ]
    exact mul_le_of_le_one_right (pow_nonneg (norm_nonneg _) _) (productA_norm_le p.1)
  have hstepsq := (sq_le_sq₀ (pow_nonneg (norm_nonneg _) _) (norm_nonneg C)).mpr hstep
  rw [threeCoupled_gradient_value _ k hk]
  change _ ≤ (k:ℝ)^2*((C.re+D.re)^2+C.im^2+D.im^2-(threeCoupledComplex threeCouplingRadius k p).re^2+
    (threeCoupledComplex threeCouplingRadius k p).im^2)
  have hh := mul_le_mul_of_nonneg_left hl (sq_nonneg (k:ℝ))
  have hs := mul_le_mul_of_nonneg_left hstepsq (sq_nonneg (k:ℝ))
  nlinarith
end


open Set Filter Function Manifold Module Metric
open scoped Topology ContDiff InnerProductSpace Matrix
local instance threeProjectionNormedSpace : NormedSpace ℝ ThreeModel := inferInstance
local instance threeProjectionContinuousSMul : ContinuousSMul ℝ ThreeModel := IsBoundedSMul.continuousSMul
lemma coordinateGradientPair_metric_point_eq {E M : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
    (g h : SmoothMetric E M) (p : M)
    (he : ∀ v w : TangentSpace 𝓘(ℝ,E) p, g.inner p v w=h.inner p v w)
    (u v : M → ℝ) : coordinateGradientPair g u v p=coordinateGradientPair h u v p := by
  have hp := (chartAt E p).left_inv (mem_chart_source E p)
  have hm : metricCoefficients g p ((chartAt E p) p)=metricCoefficients h p ((chartAt E p) p) := by
    unfold metricCoefficients
    have hh : ∀ q, q=p → ∀ a b : TangentSpace 𝓘(ℝ,E) q, g.inner q a b=h.inner q a b := by
      intro q hq; subst q; exact he
    funext i j
    exact hh _ hp _ _
  simp only [coordinateGradientPair,hm]
lemma threeCoupled_clean_abs (k : ℕ) (p : ThreeManifold) (hρ : 1/2≤‖productA p.1‖) :
    |threeCoupled threeCouplingRadius k p|≤2*‖productA p.1‖^k := by
  have hr : 0≤threeCouplingRadius := by norm_num [threeCouplingRadius]
  have hB : threeCouplingRadius*‖productB p.1‖≤‖productA p.1‖ := by
    have hb := mul_le_mul_of_nonneg_left (productB_norm_le p.1) hr
    norm_num [threeCouplingRadius] at hb
    norm_num [threeCouplingRadius]
    linarith
  have he := Complex.abs_re_le_norm (threeCoupledComplex threeCouplingRadius k p)
  change |threeCoupled threeCouplingRadius k p|≤_ at he
  have hn : ‖threeCoupledComplex threeCouplingRadius k p‖≤2*‖productA p.1‖^k := by
    unfold threeCoupledComplex
    rw [norm_mul,norm_pow,Circle.norm_coe,one_pow,mul_one]
    have hh := norm_add_le (productA p.1^k) ((threeCouplingRadius:ℂ)^k*productB p.1^k)
    simp only [norm_pow,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hr,←mul_pow] at hh
    have hpow := pow_le_pow_left₀ (mul_nonneg hr (norm_nonneg _)) hB k
    simp only [mul_pow] at hh hpow
    linarith
  exact he.trans hn
lemma threeCoupled_conjugate_gradient_lower
    (g : SmoothMetric ThreeModel ThreeManifold) (p : ThreeManifold)
    (hg : ∀ v z : TangentSpace 𝓘(ℝ,ThreeModel) p,
      g.inner p v z=threeBackgroundMetric.inner p v z)
    (k : ℕ) (hk : 1≤k) (hρ : 1/2≤‖productA p.1‖) (hρu : ‖productA p.1‖≤3/4)
    (w : ThreeManifold → ℝ) (hw : ContMDiff 𝓘(ℝ,ThreeModel) 𝓘(ℝ,ℝ) ∞ w)
    (hw0 : ∀ x, w x≠0) (hwl : 1/2≤w p) (hwu : w p≤2)
    (hGw : coordinateGradientPair g w w p≤1/4096) :
    (1/1024:ℝ)*((k:ℝ)*‖productA p.1‖^k)^2≤
      coordinateGradientPair g (fun x => threeCoupled threeCouplingRadius k x/w x)
        (fun x => threeCoupled threeCouplingRadius k x/w x) p := by
  let U := threeCoupled threeCouplingRadius k
  let u := fun x => U x/w x
  let W := ‖productA p.1‖^k
  have hu := (threeCoupled_smooth threeCouplingRadius k).div₀ hw hw0
  have he : U=fun x => w x*u x := by funext x; dsimp [u]; field_simp [hw0 x]
  have hl := threeCoupled_clean_gradient_lower k hk p hρ hρu
  rw [←coordinateGradientPair_metric_point_eq g threeBackgroundMetric p hg] at hl
  have hupper := coordinateGradientPair_mul_self_le hw hu g p
  change coordinateGradientPair g (fun y => w y*u y) (fun y => w y*u y) p≤_ at hupper
  rw [←he] at hupper
  have hU := threeCoupled_clean_abs k p hρ
  change |U p|≤2*W at hU
  have hUp : (U p)^2≤4*W^2 := by
    have hh := (sq_le_sq₀ (abs_nonneg (U p)) (by dsimp [W]; positivity : 0≤2*W)).mpr hU
    rw [sq_abs] at hh; nlinarith
  have hwl2 : 1/4≤(w p)^2 := by nlinarith
  have hwu2 : (w p)^2≤4 := by nlinarith
  have hu2 : (u p)^2≤16*W^2 := by
    have hh := mul_le_mul_of_nonneg_right hwl2 (sq_nonneg (u p))
    have heq := congrFun he p
    rw [heq,mul_pow] at hUp
    nlinarith
  have hGu := coordinateGradientPair_nonneg g u p
  have hGwn := coordinateGradientPair_nonneg g w p
  have hsmall := mul_le_mul hu2 hGw hGwn (by positivity : 0≤16*W^2)
  have hlarge := mul_le_mul_of_nonneg_right hwu2 hGu
  have hk2 : 1≤(k:ℝ)^2 := by
    have hh : (1:ℝ)≤k := by exact_mod_cast hk
    nlinarith
  have hfreq := mul_le_mul_of_nonneg_right hk2 (sq_nonneg W)
  change (1/32:ℝ)*((k:ℝ)*W)^2≤coordinateGradientPair g U U p at hl
  change coordinateGradientPair g U U p≤2*(w p)^2*coordinateGradientPair g u u p+2*(u p)^2*coordinateGradientPair g w w p at hupper
  change (1/1024:ℝ)*((k:ℝ)*W)^2≤coordinateGradientPair g u u p
  nlinarith

end YauCounterexamples
end

end OAI
