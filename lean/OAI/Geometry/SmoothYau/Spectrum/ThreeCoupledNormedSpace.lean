import Mathlib
import OAI.Geometry.SmoothYau.Smoothness.ThreeFirstNormedSpace

namespace OAI

noncomputable section
open Set Filter Function Manifold Module
open scoped Topology ContDiff InnerProductSpace Matrix
namespace YauCounterexamples
local instance threeCoupledNormedSpace : NormedSpace ℝ ThreeModel := inferInstance
local instance threeCoupledContinuousSMul : ContinuousSMul ℝ ThreeModel := IsBoundedSMul.continuousSMul
local instance threeCoupled_dimension_fact (n : ℕ) : Fact (Module.finrank ℝ (Euclidean (n+1))=n+1) := ⟨by simp [Euclidean]⟩
abbrev productAxis (i : Fin 3) : Euclidean 3 := EuclideanSpace.single i 1
lemma productAxis_inner (i j : Fin 3) : inner ℝ (productAxis i) (productAxis j) = if i=j then 1 else 0 := by
  simp [productAxis,EuclideanSpace.inner_single_left,PiLp.single_apply]
lemma productAxis_coord (i : Fin 3) (x : Euclidean 3) : inner ℝ (productAxis i) x = x i := by
  simp [productAxis,EuclideanSpace.inner_single_left]
lemma productAxis_norm (i : Fin 3) : ‖productAxis i‖=1 := by simp [productAxis]
def productA (x : Euclidean 3) : ℂ := planarLinear (productAxis 0) (productAxis 1) x
def productB (x : Euclidean 3) : ℂ := planarLinear (productAxis 0) (productAxis 2) x
lemma productA_re (x : Euclidean 3) : (productA x).re=x 0 := by simp [productA,planarLinear,productAxis_coord]
lemma productA_im (x : Euclidean 3) : (productA x).im=x 1 := by simp [productA,planarLinear,productAxis_coord]
lemma productB_re (x : Euclidean 3) : (productB x).re=x 0 := by simp [productB,planarLinear,productAxis_coord]
lemma productB_im (x : Euclidean 3) : (productB x).im=x 2 := by simp [productB,planarLinear,productAxis_coord]
lemma productAB_nonzero (x : Sphere 2) : productA x ≠ 0 ∨ productB x ≠ 0 := by
  by_contra h
  push Not at h
  have hx0 := congrArg Complex.re h.1
  have hx1 := congrArg Complex.im h.1
  have hx2 := congrArg Complex.im h.2
  simp only [productA_re,productA_im,productB_im,Complex.zero_re,Complex.zero_im] at hx0 hx1 hx2
  have hz : (x:Euclidean 3)=0 := by ext i; fin_cases i <;> assumption
  have hn : ‖(x:Euclidean 3)‖=1 := by simpa only [Metric.mem_sphere,dist_zero_right] using x.property
  simp [hz] at hn

def threeCoupledComplex (r : ℝ) (k : ℕ) (p : ThreeManifold) : ℂ :=
  (productA p.1^k+(r:ℂ)^k*productB p.1^k)*(p.2:ℂ)^k
def threeCoupled (r : ℝ) (k : ℕ) (p : ThreeManifold) : ℝ := (threeCoupledComplex r k p).re
lemma threeCoupled_eq (r : ℝ) (k : ℕ) : threeCoupled r k =
    fun p => threePower (productAxis 0) (productAxis 1) k p+r^k*threePower (productAxis 0) (productAxis 2) k p := by
  funext p
  simp only [threeCoupled,threeCoupledComplex,add_mul,mul_assoc,Complex.add_re,
    ←Complex.ofReal_pow,Complex.re_ofReal_mul,threePower,threeComplexPower,productA,productB]
lemma threeCoupled_smooth (r : ℝ) (k : ℕ) : ContMDiff 𝓘(ℝ,ThreeModel) 𝓘(ℝ,ℝ) ∞ (threeCoupled r k) := by
  rw [threeCoupled_eq]
  exact (threePower_smooth _ _ _).add (contMDiff_const.mul (threePower_smooth _ _ _))

lemma product_laplace_const_mul (g : SmoothMetric ThreeModel ThreeManifold)
    {u : ThreeManifold → ℝ} (hu : ContMDiff 𝓘(ℝ,ThreeModel) 𝓘(ℝ,ℝ) 2 u)
    (c : ℝ) (x : ThreeManifold) :
    laplaceBeltrami g (fun y => c*u y) x=c*laplaceBeltrami g u x := by
  have h := complexLaplaceBeltrami_const_mul (Complex.ofRealCLM.contMDiff.comp hu) (c:ℂ) g x
  change complexLaplaceBeltrami g (fun y => (c:ℂ)*(u y:ℂ)) x=(c:ℂ)*complexLaplaceBeltrami g (fun y => (u y:ℂ)) x at h
  have he : (fun y => (c:ℂ)*(u y:ℂ))=fun y => ((c*u y:ℝ):ℂ) := by ext y; simp
  rw [he,complexLaplaceBeltrami_ofReal,complexLaplaceBeltrami_ofReal] at h
  exact_mod_cast h
lemma product_laplace_linear_eigen (g : SmoothMetric ThreeModel ThreeManifold)
    (u v : ThreeManifold → ℝ) (hu : ContMDiff 𝓘(ℝ,ThreeModel) 𝓘(ℝ,ℝ) 2 u)
    (hv : ContMDiff 𝓘(ℝ,ThreeModel) 𝓘(ℝ,ℝ) 2 v) (c Λ : ℝ) (p : ThreeManifold)
    (he₁ : -laplaceBeltrami g u p=Λ*u p) (he₂ : -laplaceBeltrami g v p=Λ*v p) :
    -laplaceBeltrami g (fun x => u x+c*v x) p=Λ*(u p+c*v p) := by
  have hcv : ContMDiff 𝓘(ℝ,ThreeModel) 𝓘(ℝ,ℝ) 2 (fun x => c*v x) := contMDiff_const.mul hv
  have hadd := laplaceBeltrami_add hu hcv g p
  have hmul := product_laplace_const_mul g hv c p
  calc
    _ = -(laplaceBeltrami g u p+laplaceBeltrami g (fun x => c*v x) p) := congrArg Neg.neg hadd
    _ = -(laplaceBeltrami g u p+c*laplaceBeltrami g v p) := congrArg (fun z : ℝ => -(laplaceBeltrami g u p+z)) hmul
    _ = _ := by linear_combination he₁+c*he₂
lemma threeCoupled_eigen (r : ℝ) (k : ℕ) (hk : 2 ≤ k) (p : ThreeManifold) :
    -laplaceBeltrami threeBackgroundMetric (threeCoupled r k) p=productFrequency k*threeCoupled r k p := by
  have ha : inner ℝ (productAxis 0) (productAxis 0)=1 := by simp
  have hb : inner ℝ (productAxis 1) (productAxis 1)=1 := by simp
  have hc : inner ℝ (productAxis 2) (productAxis 2)=1 := by simp
  have hab : inner ℝ (productAxis 0) (productAxis 1)=0 := by norm_num [productAxis_inner,Fin.ext_iff]
  have hac : inner ℝ (productAxis 0) (productAxis 2)=0 := by norm_num [productAxis_inner,Fin.ext_iff]
  have h₁ := threePower_eigen _ _ k hk ha hb hab p
  have h₂ := threePower_eigen _ _ k hk ha hc hac p
  have h2 : (2:WithTop ℕ∞) ≤ ∞ := le_of_lt (WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top 2))
  rw [threeCoupled_eq]
  exact product_laplace_linear_eigen threeBackgroundMetric _ _
    ((threePower_smooth _ _ _).of_le h2) ((threePower_smooth _ _ _).of_le h2) (r^k) _ p h₁ h₂
lemma threeCoupled_chart_smooth (r : ℝ) (k : ℕ) (p : ThreeManifold) :
    ContDiff ℝ ∞ (threeCoupled r k ∘ (chartAt ThreeModel p).symm) := by
  rw [threeCoupled_eq]
  change ContDiff ℝ ∞ (fun y => (threePower (productAxis 0) (productAxis 1) k ∘ (chartAt ThreeModel p).symm) y +
    r^k*(threePower (productAxis 0) (productAxis 2) k ∘ (chartAt ThreeModel p).symm) y)
  exact (Complex.reCLM.contDiff.comp (threeComplexPower_chart_smooth _ _ _ _)).add
    (contDiff_const.mul (Complex.reCLM.contDiff.comp (threeComplexPower_chart_smooth _ _ _ _)))
lemma threeCoupled_chart_first (r : ℝ) (k : ℕ) (p : ThreeManifold) (v : ThreeModel) :
    fderiv ℝ (threeCoupled r k ∘ (chartAt ThreeModel p).symm) 0 v =
      ((k:ℂ)*(p.2:ℂ)^k*(productA p.1^(k-1)*productA (unitSphereFrame (n:=2) p.1 v.fst)+
        (r:ℂ)^k*productB p.1^(k-1)*productB (unitSphereFrame (n:=2) p.1 v.fst))+
      (k:ℂ)*(p.2:ℂ)^(k-1)*unitSphereFrame (n:=1) p.2 v.snd*
        (productA p.1^k+(r:ℂ)^k*productB p.1^k)).re := by
  rw [threeCoupled_eq]
  change fderiv ℝ (fun y => (threePower (productAxis 0) (productAxis 1) k ∘ (chartAt ThreeModel p).symm) y +
    r^k*(threePower (productAxis 0) (productAxis 2) k ∘ (chartAt ThreeModel p).symm) y) 0 v = _
  have ha := (Complex.reCLM.contDiff.comp (threeComplexPower_chart_smooth (productAxis 0) (productAxis 1) k p)).differentiable (by simp)
  have hb := (Complex.reCLM.contDiff.comp (threeComplexPower_chart_smooth (productAxis 0) (productAxis 2) k p)).differentiable (by simp)
  erw [fderiv_fun_add (ha 0) ((differentiableAt_const _).mul (hb 0)),fderiv_const_mul (hb 0)]
  simp only [add_apply,smul_apply,smul_eq_mul]
  erw [threePower_chart_first,threePower_chart_first]
  rw [←Complex.re_ofReal_mul,←Complex.add_re]
  apply congrArg Complex.re
  change _ = (k:ℂ)*(p.2:ℂ)^k*(planarLinear _ _ _^(k-1)*planarLinear _ _ _+
        (r:ℂ)^k*planarLinear _ _ _^(k-1)*planarLinear _ _ _)+
      (k:ℂ)*(p.2:ℂ)^(k-1)*unitSphereFrame (n:=1) p.2 v.snd*
        (planarLinear _ _ _^k+(r:ℂ)^k*planarLinear _ _ _^k)
  push_cast
  ring
end YauCounterexamples
end

end OAI
