import Mathlib
import OAI.Probability.ParisiFinite.ParisiReflection

namespace OAI

/-! Parisi Hankel Derivative. -/

noncomputable section

open MeasureTheory Set Filter
open scoped Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal
open MeasureTheory ProbabilityTheory Filter Function Set
open MeasureTheory ProbabilityTheory Filter Function Set Real
open scoped Topology NNReal
open MeasureTheory ProbabilityTheory Set Real Matrix Filter InnerProductSpace
open scoped Topology NNReal RealInnerProductSpace BigOperators
namespace ParisiSpectral

lemma posSemidef_anchor {A : Type*} {K : Matrix A A ℝ} (hK : K.PosSemidef) (z : A) :
    Matrix.PosSemidef (fun x y => K x y-K x z-K z y+K z z) := by
  let : Fact K.PosSemidef := ⟨hK⟩
  have hh := posSemidef_inner (fun x => kernelFeature K x-kernelFeature K z)
  have he (x y : A) : ⟪kernelFeature K x-kernelFeature K z,kernelFeature K y-kernelFeature K z⟫_ℝ=
      K x y-K x z-K z y+K z z := by
    rw [inner_sub_left,inner_sub_right,inner_sub_right]
    simp only [inner_kernelFeature]
    ring
  simpa only [he] using hh

def HankelCPD (f : ℝ → ℝ) (s : Set ℝ) : Prop :=
  ∀ z : s,Matrix.PosSemidef (fun x y : s => f ((x+y)/2)-f ((x+z)/2)-f ((z+y)/2)+f z)

def HankelPD (f : ℝ → ℝ) (s : Set ℝ) : Prop :=
  Matrix.PosSemidef (fun x y : s => f ((x+y)/2))

lemma HankelPD.cpd {f : ℝ → ℝ} {s : Set ℝ} (hf : HankelPD f s) : HankelCPD f s := by
  intro z
  convert posSemidef_anchor hf z using 1
  simp only [add_self_div_two]

lemma scaled_taylorOn_tendsto {f : ℝ → ℝ} {s : Set ℝ} {n : ℕ}
    (hs : Convex ℝ s) (hso : IsOpen s) (hf : ContDiffOn ℝ n f s) {x : ℝ} (hx : x∈s) (k : ℝ) :
    Tendsto (fun e => (f (x+k*e)-taylorWithinEval f n s x (x+k*e))/e^n) (𝓝 (0:ℝ)) (𝓝 0) := by
  have ht := Real.taylor_tendsto hs hx hf
  rw [hso.nhdsWithin_eq hx] at ht
  have hc : Tendsto (fun e : ℝ => x+k*e) (𝓝 0) (𝓝 x) := by
    simpa only [mul_zero,add_zero] using
      ((show Continuous (fun e : ℝ => x+k*e) from by fun_prop).tendsto (0:ℝ))
  have hh := (ht.comp hc).const_mul (k^n)
  simp only [mul_zero] at hh
  apply hh.congr
  intro e
  dsimp only [Function.comp_def]
  rw [add_sub_cancel_left,mul_pow]
  by_cases hk : k=0
  · simp [hk,taylorWithinEval_self]
  · field_simp

lemma secondForward_tendsto {f : ℝ → ℝ} {s : Set ℝ}
    (hs : Convex ℝ s) (hso : IsOpen s) (hf : ContDiffOn ℝ 2 f s) {x : ℝ} (hx : x∈s) :
    Tendsto (fun e => (f (x+e)-2*f (x+e/2)+f x)/e^2) (𝓝[≠] (0:ℝ))
      (𝓝 (iteratedDeriv 2 f x/4)) := by
  have h1 := scaled_taylorOn_tendsto hs hso hf hx 1
  have h2 := (scaled_taylorOn_tendsto hs hso hf hx (1/2)).const_mul 2
  have hh := (h1.sub h2).mono_left (nhdsWithin_le_nhds : 𝓝[≠] (0:ℝ)≤𝓝 0)
  simp only [sub_zero,mul_zero,one_mul] at hh
  have he : (fun e : ℝ => (f (x+e)-taylorWithinEval f 2 s x (x+e))/e^2-
      2*((f (x+(1/2)*e)-taylorWithinEval f 2 s x (x+(1/2)*e))/e^2)) =ᶠ[𝓝[≠] 0]
      (fun e => (f (x+e)-2*f (x+e/2)+f x)/e^2-iteratedDeriv 2 f x/4) := by
    filter_upwards [self_mem_nhdsWithin] with e he
    have hne : e≠0 := he
    have hd (n : ℕ) : iteratedDerivWithin n f s x=iteratedDeriv n f x :=
      iteratedDerivWithin_of_isOpen hso hx
    simp only [taylorWithinEval_succ,taylor_within_zero_eval,hd]
    norm_num
    field_simp
    ring
  have hl := hh.congr' he
  have ha := hl.add_const (iteratedDeriv 2 f x/4)
  simpa only [sub_add_cancel,zero_add] using ha

lemma HankelCPD.secondDeriv {f : ℝ → ℝ} {s : Set ℝ}
    (h : HankelCPD f s) (hs : Convex ℝ s) (hso : IsOpen s)
    (hne : s.Nonempty) (hf : ContDiffOn ℝ 2 f s) :
    HankelPD (iteratedDeriv 2 f) s := by
  classical
  let z : s := ⟨hne.choose,hne.choose_spec⟩
  let K : Matrix s s ℝ := fun x y => f ((x+y)/2)-f ((x+z)/2)-f ((z+y)/2)+f z
  let : Fact K.PosSemidef := ⟨h z⟩
  let T (e : ℝ) (x : s) : s := if hx : (x:ℝ)+e∈s then ⟨x+e,hx⟩ else x
  let G (e : ℝ) (x : s) := e⁻¹ • (kernelFeature K (T e x)-kernelFeature K x)
  have hlim (x y : s) : Tendsto (fun e => ⟪G e x,G e y⟫_ℝ) (𝓝[≠] (0:ℝ))
      (𝓝 (iteratedDeriv 2 f ((x+y)/2)/4)) := by
    have hxy : ((x:ℝ)+y)/2∈s := by
      simpa only [midpoint_eq_smul_add,smul_eq_mul,invOf_eq_inv,div_eq_mul_inv,mul_comm] using hs.midpoint_mem x.property y.property
    have hh := secondForward_tendsto hs hso hf hxy
    apply hh.congr'
    have hx : ∀ᶠ e in 𝓝 (0:ℝ),(x:ℝ)+e∈s := by
      have hh := (show Continuous (fun e : ℝ => (x:ℝ)+e) from by fun_prop).tendsto (0:ℝ)
      simp only [add_zero] at hh
      exact hh.eventually (hso.mem_nhds x.property)
    have hy : ∀ᶠ e in 𝓝 (0:ℝ),(y:ℝ)+e∈s := by
      have hh := (show Continuous (fun e : ℝ => (y:ℝ)+e) from by fun_prop).tendsto (0:ℝ)
      simp only [add_zero] at hh
      exact hh.eventually (hso.mem_nhds y.property)
    filter_upwards [hx.filter_mono nhdsWithin_le_nhds,hy.filter_mono nhdsWithin_le_nhds]
      with e heX heY
    simp only [G,real_inner_smul_left,real_inner_smul_right,inner_sub_left,inner_sub_right,
      inner_kernelFeature]
    simp only [T,dite_eq_left heX,dite_eq_left heY,K]
    have he1 : ((x:ℝ)+e+(y+e))/2=((x:ℝ)+y)/2+e := by ring
    have he2 : ((x:ℝ)+e+y)/2=((x:ℝ)+y)/2+e/2 := by ring
    have he3 : ((x:ℝ)+(y+e))/2=((x:ℝ)+y)/2+e/2 := by ring
    rw [he1,he2,he3]
    ring
  have hh := PositiveDefinite.posSemidef_limit (l := 𝓝[≠] (0:ℝ))
    (fun e => posSemidef_inner (G e)) hlim
  have hp := hh.smul (show (0:ℝ)≤4 by norm_num)
  have heq : Matrix.of (fun x y : s => iteratedDeriv 2 f ((x+y)/2)) =
      (4:ℝ) • Matrix.of (fun x y : s => iteratedDeriv 2 f ((x+y)/2)/4) := by
    ext x y
    simp only [Matrix.smul_apply,Matrix.of_apply,smul_eq_mul]
    ring
  change (Matrix.of (fun x y : s => iteratedDeriv 2 f ((x+y)/2))).PosSemidef
  rw [heq]
  exact hp

lemma HankelCPD.add {f g : ℝ → ℝ} {s : Set ℝ}
    (hf : HankelCPD f s) (hg : HankelCPD g s) : HankelCPD (fun x => f x+g x) s := by
  intro z
  have he : Matrix.of (fun x y : s =>
      (f ((x+y)/2)+g ((x+y)/2))-(f ((x+z)/2)+g ((x+z)/2))-
      (f ((z+y)/2)+g ((z+y)/2))+(f z+g z)) =
      Matrix.of (fun x y : s => f ((x+y)/2)-f ((x+z)/2)-f ((z+y)/2)+f z)+
      Matrix.of (fun x y : s => g ((x+y)/2)-g ((x+z)/2)-g ((z+y)/2)+g z) := by
    ext x y
    simp only [Matrix.add_apply,Matrix.of_apply]
    ring
  change (Matrix.of (fun x y : s =>
      (f ((x+y)/2)+g ((x+y)/2))-(f ((x+z)/2)+g ((x+z)/2))-
      (f ((z+y)/2)+g ((z+y)/2))+(f z+g z))).PosSemidef
  rw [he]
  exact (hf z).add (hg z)

lemma HankelCPD.of_rightQuotient {F : ℝ → ℝ → ℝ} {f : ℝ → ℝ} {s : Set ℝ} {C : ℝ}
    (hs : Convex ℝ s) (hF : ∀ r,0<r → HankelPD (F r) s)
    (ht : ∀ x∈s,Tendsto (fun r => (F r x-C)/r) (𝓝[>] (0:ℝ)) (𝓝 (f x))) :
    HankelCPD f s := by
  classical
  intro z
  let K (r : ℝ) : Matrix s s ℝ := if 0<r then
    Matrix.of (fun x y => (F r ((x+y)/2)-F r ((x+z)/2)-F r ((z+y)/2)+F r z)/r) else 0
  have hK (r : ℝ) : (K r).PosSemidef := by
    dsimp only [K]
    split_ifs with hr
    · have he : Matrix.of (fun x y : s => (F r ((x+y)/2)-F r ((x+z)/2)-F r ((z+y)/2)+F r z)/r)=
          r⁻¹ • Matrix.of (fun x y : s => F r ((x+y)/2)-F r ((x+z)/2)-F r ((z+y)/2)+F r z) := by
        ext x y
        simp only [Matrix.smul_apply,Matrix.of_apply,smul_eq_mul,div_eq_mul_inv,mul_comm]
      rw [he]
      exact ((hF r hr).cpd z).smul (inv_nonneg.mpr hr.le)
    · exact Matrix.PosSemidef.zero
  apply PositiveDefinite.posSemidef_limit (l := 𝓝[>] (0:ℝ)) hK
  intro x y
  have hm (u v : s) : ((u:ℝ)+v)/2∈s := by
    simpa only [midpoint_eq_smul_add,smul_eq_mul,invOf_eq_inv,div_eq_mul_inv,mul_comm]
      using hs.midpoint_mem u.property v.property
  have hh := (((ht _ (hm x y)).sub (ht _ (hm x z))).sub (ht _ (hm z y))).add (ht z z.property)
  apply hh.congr'
  filter_upwards [self_mem_nhdsWithin] with r hr
  dsimp only [K]
  rw [ite_eq_left (show 0<r from hr)]
  simp only [Matrix.of_apply]
  ring

lemma HankelPD.midpoint_le {f : ℝ → ℝ} {s : Set ℝ} (hf : HankelPD f s)
    {x y : ℝ} (hx : x∈s) (hy : y∈s) : 2*f ((x+y)/2)≤f x+f y := by
  let K : Matrix s s ℝ := fun u v => f ((u+v)/2)
  let : Fact K.PosSemidef := ⟨hf⟩
  have hh := norm_kernelFeature_sub_sq K ⟨x,hx⟩ ⟨y,hy⟩
  simp only [K,add_self_div_two] at hh
  nlinarith [sq_nonneg ‖kernelFeature K ⟨x,hx⟩-kernelFeature K ⟨y,hy⟩‖]

lemma HankelPD.midpoint_lt {f : ℝ → ℝ} {s : Set ℝ} (hf : HankelPD f s)
    {x y : ℝ} (hx : x∈s) (hy : y∈s) (hne : f x≠f y) : 2*f ((x+y)/2)<f x+f y := by
  let K : Matrix s s ℝ := fun u v => f ((u+v)/2)
  let : Fact K.PosSemidef := ⟨hf⟩
  have hh := norm_kernelFeature_sub_sq K ⟨x,hx⟩ ⟨y,hy⟩
  simp only [K,add_self_div_two] at hh
  have hn : kernelFeature K ⟨x,hx⟩≠kernelFeature K ⟨y,hy⟩ := by
    intro he
    apply hne
    have hh := congrArg (fun v => ‖v‖^2) he
    rw [norm_kernelFeature_sq K,norm_kernelFeature_sq K] at hh
    simpa only [K,add_self_div_two] using hh
  have hp := sq_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hn))
  linarith

end ParisiSpectral

 

 

open MeasureTheory ProbabilityTheory Set Real Matrix Filter InnerProductSpace
open scoped Topology NNReal RealInnerProductSpace BigOperators
namespace ParisiSpectral

lemma posSemidef_weight {A : Type*} {K : Matrix A A ℝ} (hK : K.PosSemidef) (w : A → ℝ) :
    Matrix.PosSemidef (Matrix.of (fun x y => w x*w y*K x y)) := by
  let : Fact K.PosSemidef := ⟨hK⟩
  have hh := posSemidef_inner (fun x => w x • kernelFeature K x)
  have he : Matrix.of (fun x y => w x*w y*K x y)=
      Matrix.of (fun x y => ⟪w x • kernelFeature K x,w y • kernelFeature K y⟫_ℝ) := by
    ext x y
    simp only [Matrix.of_apply,real_inner_smul_left,real_inner_smul_right,inner_kernelFeature]
    ring
  rw [he]
  exact hh

 

lemma hankelPD_heat_observation {μ : Measure ℝ} [IsFiniteMeasure μ] (hμ : PositiveOnPD μ)
    {F : ℝ → ℝ → ℝ} {a : ℝ} {s : Set ℝ} (hs : ∀ t∈s,a≤t) (hsv : Convex ℝ s)
    (hc : ∀ t∈s,Continuous (F t))
    (hK : Matrix.PosSemidef (Matrix.of (fun p q : s × ℝ => F ((p.1+q.1)/2) (p.2-q.2)))) :
    HankelPD (fun t => ∫ x,heat (toNNReal (t-a)) (F t) x ∂μ) s := by
  let κ : s → s → ℝ → ℝ := fun t u x => F ((t+u)/2) x
  have hmid (t u : s) : ((t:ℝ)+u)/2∈s := by
    simpa only [midpoint_eq_smul_add,smul_eq_mul,invOf_eq_inv,div_eq_mul_inv,mul_comm]
      using hsv.midpoint_mem t.property u.property
  have hκc (t u : s) : Continuous (κ t u) := hc _ (hmid t u)
  have hp := stationary_kernel_heat κ hK hκc (fun t => toNNReal ((t-a)/2))
  have he (t u : s) : toNNReal (((t:ℝ)-a)/2)+toNNReal (((u:ℝ)-a)/2)=
      toNNReal (((t:ℝ)+u)/2-a) := by
    apply NNReal.eq
    rw [NNReal.coe_add,coe_toNNReal _ (by linarith [hs t t.property]),
      coe_toNNReal _ (by linarith [hs u u.property]),coe_toNNReal _ (by linarith [hs t t.property,hs u u.property])]
    ring
  let κ' : s → s → ℝ → ℝ := fun t u x => heat (toNNReal (((t:ℝ)+u)/2-a)) (κ t u) x
  have hc' (t u : s) : Continuous (κ' t u) :=
    continuous_heat (hκc t u) (stationary_kernel_bounded κ hK t u) _
  have hp' : Matrix.PosSemidef (Matrix.of (fun p q : s × ℝ => κ' p.1 q.1 (p.2-q.2))) := by
    change (Matrix.of (fun p q : s × ℝ => heat (toNNReal (((p.1:ℝ)-a)/2)+toNNReal (((q.1:ℝ)-a)/2)) (κ p.1 q.1) (p.2-q.2))).PosSemidef at hp
    simpa only [he,κ'] using hp
  have hi (t u : s) : Integrable (κ' t u) μ := Integrable.of_bound (hc' t u).aestronglyMeasurable _
    (ae_of_all _ (stationary_kernel_bounded κ' hp' t u))
  exact hμ.kernel_integral κ' hp' hc' hi (fun t u => by dsimp only [κ',κ]; rw [add_comm (t:ℝ) (u:ℝ)])

def backwardC (d K α t x : ℝ) : ℝ := K*exp (α^2/2*(d-t))*cosh (α*x)
def backwardG (d : ℝ) (g : ℝ → ℝ) (t x : ℝ) : ℝ := heat (toNNReal (d-t)) g x

lemma backwardG_reflection {g : ℝ → ℝ} (hg : PositiveDefinite g) (hc : Continuous g)
    {d : ℝ} {s : Set ℝ} (hs : ∀ t∈s,t≤d) :
    Matrix.PosSemidef (Matrix.of (fun p q : s × ℝ => backwardG d g ((p.1+q.1)/2) (p.2-q.2))) := by
  have hh := (hg.heat_reflection hc).submatrix (fun p : s × ℝ => (toNNReal ((d-p.1)/2),p.2))
  have he (p q : s × ℝ) : toNNReal ((d-(p.1:ℝ))/2)+toNNReal ((d-(q.1:ℝ))/2)=
      toNNReal (d-((p.1:ℝ)+q.1)/2) := by
    apply NNReal.eq
    rw [NNReal.coe_add,coe_toNNReal _ (by linarith [hs p.1 p.1.property]),
      coe_toNNReal _ (by linarith [hs q.1 q.1.property]),
      coe_toNNReal _ (by linarith [hs p.1 p.1.property,hs q.1 q.1.property])]
    ring
  change (Matrix.of (fun p q : s × ℝ => heat (toNNReal ((d-p.1)/2)+toNNReal ((d-q.1)/2)) g (p.2-q.2))).PosSemidef at hh
  simpa only [he,backwardG] using hh

lemma backwardC_neg_rpow {d K α r : ℝ} (hK : 0<K) (hr : 0<r) (s : Set ℝ) :
    Matrix.PosSemidef (Matrix.of (fun p q : s × ℝ => (backwardC d K α ((p.1+q.1)/2) (p.2-q.2))^(-r))) := by
  have hp := (cosh_neg_rpow_positiveDefinite hr α).submatrix (fun p : s × ℝ => p.2)
  have hw := (posSemidef_weight hp (fun p : s × ℝ => exp (-r*α^2/4*(d-p.1)))).smul
    (rpow_nonneg hK.le (-r))
  have he : Matrix.of (fun p q : s × ℝ => (backwardC d K α ((p.1+q.1)/2) (p.2-q.2))^(-r))=
      K^(-r) • Matrix.of (fun p q : s × ℝ => exp (-r*α^2/4*(d-p.1))*
        exp (-r*α^2/4*(d-q.1))*(cosh (α*(p.2-q.2)))^(-r)) := by
    ext p q
    simp only [Matrix.smul_apply,Matrix.of_apply,smul_eq_mul,backwardC]
    rw [mul_rpow (mul_pos hK (exp_pos _)).le (cosh_pos _).le,
      mul_rpow hK.le (exp_pos _).le,←exp_mul,←mul_assoc,←exp_add]
    congr 2
    ring_nf
  rw [he]
  exact hw
end ParisiSpectral

 

 

open MeasureTheory ProbabilityTheory Set Real Filter
open scoped Topology NNReal
namespace ParisiSpectral

lemma exp_abs_shift_le {M : ℝ} (hM : 0≤M) (x s z : ℝ) :
    exp (M*|x+s*z|)≤exp (M*|x|)*exp (M*|s| *|z|) := by
  rw [←exp_add]
  apply exp_le_exp.mpr
  have hh := mul_le_mul_of_nonneg_left (abs_add_le x (s*z)) hM
  simpa only [abs_mul,mul_add,mul_assoc] using hh

lemma exp_abs_shift_near_le {M : ℝ} (hM : 0≤M) (x s z : ℝ) {r : ℝ} (hr : |r-s|≤1) :
    exp (M*|x+r*z|)≤exp (M*|x|)*exp (M*(|s|+1)*|z|) := by
  have hb : |r|≤|s|+1 := by have := abs_add_le (r-s) s; rw [sub_add_cancel] at this; linarith
  exact (exp_abs_shift_le hM x r z).trans (mul_le_mul_of_nonneg_left
    (exp_le_exp.mpr (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hb hM) (abs_nonneg z))) (exp_pos _).le)

lemma integrable_scale_prod {μ : Measure ℝ} [IsFiniteMeasure μ] {f : ℝ → ℝ}
    (hc : Continuous f) {M C : ℝ} (hM : 0≤M) (hC : 0≤C)
    (hf : ∀ x,|f x|≤C*exp (M*|x|)) (hi : Integrable (fun x => exp (M*|x|)) μ) (s : ℝ) :
    Integrable (fun p : ℝ × ℝ => f (p.1+s*p.2)) (μ.prod (gaussianReal 0 1)) := by
  have hh := (hi.const_mul C).mul_prod (ParisiFinite.integrable_exp_abs (M*|s|))
  apply hh.mono' (by fun_prop)
  filter_upwards [] with p
  rw [Real.norm_eq_abs]
  exact (hf _).trans (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (exp_abs_shift_le hM p.1 s p.2) hC)

lemma integrable_coord_scale_prod {μ : Measure ℝ} [IsFiniteMeasure μ] {f : ℝ → ℝ}
    (hc : Continuous f) {M C : ℝ} (hM : 0≤M) (hC : 0≤C)
    (hf : ∀ x,|f x|≤C*exp (M*|x|)) (hi : Integrable (fun x => exp (M*|x|)) μ) (s : ℝ) :
    Integrable (fun p : ℝ × ℝ => p.2*f (p.1+s*p.2)) (μ.prod (gaussianReal 0 1)) := by
  have hh := (hi.const_mul C).mul_prod (ParisiFinite.integrable_exp_abs (M*|s|+1))
  apply hh.mono' (by fun_prop)
  filter_upwards [] with p
  rw [Real.norm_eq_abs,abs_mul]
  calc
    |p.2| *|f (p.1+s*p.2)| ≤ |p.2| *(C*(exp (M*|p.1|) * exp (M*|s| *|p.2|))) :=
      mul_le_mul_of_nonneg_left ((hf _).trans (mul_le_mul_of_nonneg_left (exp_abs_shift_le hM _ _ _) hC)) (abs_nonneg _)
    _ = C*exp (M*|p.1|)*(|p.2| *exp (M*|s| *|p.2|)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (ParisiFinite.abs_mul_exp_le (M*|s|) p.2) (by positivity)

lemma hasDerivAt_scale_prod {μ : Measure ℝ} [IsFiniteMeasure μ] {f f' : ℝ → ℝ}
    (hc : Continuous f) (hc' : Continuous f') (hd : ∀ x,HasDerivAt f (f' x) x)
    {M C D : ℝ} (hM : 0≤M) (hC : 0≤C) (hD : 0≤D)
    (hf : ∀ x,|f x|≤C*exp (M*|x|)) (hf' : ∀ x,|f' x|≤D*exp (M*|x|))
    (hi : Integrable (fun x => exp (M*|x|)) μ) (s : ℝ) :
    HasDerivAt (fun r => ∫ p : ℝ × ℝ,f (p.1+r*p.2) ∂μ.prod (gaussianReal 0 1))
      (∫ p : ℝ × ℝ,p.2*f' (p.1+s*p.2) ∂μ.prod (gaussianReal 0 1)) s := by
  apply (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (s := Metric.ball s 1) (bound := fun p : ℝ × ℝ => D*exp (M*|p.1|) * exp ((M*(|s|+1)+1)*|p.2|))
    (F' := fun r p => p.2*f' (p.1+r*p.2))
    (Metric.ball_mem_nhds _ (by norm_num))
    (Eventually.of_forall (fun r => by fun_prop)) (integrable_scale_prod hc hM hC hf hi s)
    (by fun_prop) ?_
    ((hi.const_mul D).mul_prod (ParisiFinite.integrable_exp_abs (M*(|s|+1)+1))) ?_).2
  · exact ae_of_all _ fun p r hr => by
      rw [Real.norm_eq_abs,abs_mul]
      calc
        |p.2| *|f' (p.1+r*p.2)| ≤ |p.2| *(D*(exp (M*|p.1|) * exp (M*(|s|+1)*|p.2|))) :=
          mul_le_mul_of_nonneg_left ((hf' _).trans (mul_le_mul_of_nonneg_left
            (exp_abs_shift_near_le hM p.1 s p.2 (by simpa [Real.dist_eq] using hr.le)) hD)) (abs_nonneg _)
        _ = D*exp (M*|p.1|)*(|p.2| *exp (M*(|s|+1)*|p.2|)) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left (ParisiFinite.abs_mul_exp_le (M*(|s|+1)) p.2) (by positivity)
  · exact ae_of_all _ fun p r _ => by
      simpa only [Function.comp_def,id_eq,one_mul,mul_one,mul_comm] using (hd (p.1+r*p.2)).comp r (((hasDerivAt_id r).mul_const p.2).const_add p.1)

lemma integrable_scale_gaussian {f : ℝ → ℝ} (hc : Continuous f)
    {M C : ℝ} (hM : 0≤M) (hC : 0≤C) (hf : ∀ x,|f x|≤C*exp (M*|x|)) (x s : ℝ) :
    Integrable (fun z => f (x+s*z)) (gaussianReal 0 1) := by
  apply ((ParisiFinite.integrable_exp_abs (M*|s|)).const_mul (C*exp (M*|x|))).mono' (by fun_prop)
  filter_upwards [] with z
  rw [Real.norm_eq_abs]
  exact (hf _).trans (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (exp_abs_shift_le hM x s z) hC)

lemma integrable_coord_scale_gaussian {f : ℝ → ℝ} (hc : Continuous f)
    {M C : ℝ} (hM : 0≤M) (hC : 0≤C) (hf : ∀ x,|f x|≤C*exp (M*|x|)) (x s : ℝ) :
    Integrable (fun z => z*f (x+s*z)) (gaussianReal 0 1) := by
  apply ((ParisiFinite.integrable_exp_abs (M*|s|+1)).const_mul (C*exp (M*|x|))).mono' (by fun_prop)
  filter_upwards [] with z
  rw [Real.norm_eq_abs,abs_mul]
  calc
    |z| *|f (x+s*z)| ≤ |z| *(C*(exp (M*|x|)*exp (M*|s| *|z|))) :=
      mul_le_mul_of_nonneg_left ((hf _).trans (mul_le_mul_of_nonneg_left (exp_abs_shift_le hM _ _ _) hC)) (abs_nonneg _)
    _ = C*exp (M*|x|)*(|z| *exp (M*|s| *|z|)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (ParisiFinite.abs_mul_exp_le (M*|s|) z) (by positivity)

lemma scale_gaussian_ibp {f f' : ℝ → ℝ} (hc : Continuous f) (hc' : Continuous f')
    (hd : ∀ x,HasDerivAt f (f' x) x) {M C D : ℝ} (hM : 0≤M) (hC : 0≤C) (hD : 0≤D)
    (hf : ∀ x,|f x|≤C*exp (M*|x|)) (hf' : ∀ x,|f' x|≤D*exp (M*|x|)) (x s : ℝ) :
    (∫ z,z*f (x+s*z) ∂gaussianReal 0 1)=s*∫ z,f' (x+s*z) ∂gaussianReal 0 1 := by
  have hh := SKGaussian.integral_mul_eq_integral_deriv (f := fun z => f (x+s*z))
    (f' := fun z => s*f' (x+s*z))
    (fun z => by simpa only [Function.comp_def,id_eq,mul_one,mul_comm] using (hd (x+s*z)).comp z (((hasDerivAt_id z).const_mul s).const_add x))
    (integrable_scale_gaussian hc hM hC hf x s)
    ((integrable_scale_gaussian hc' hM hD hf' x s).const_mul s)
    (integrable_coord_scale_gaussian hc hM hC hf x s)
  simpa only [integral_const_mul] using hh

lemma hasDerivAt_scale_prod_second {μ : Measure ℝ} [IsFiniteMeasure μ] {f f' f'' : ℝ → ℝ}
    (hc : Continuous f) (hc' : Continuous f') (hc'' : Continuous f'')
    (hd : ∀ x,HasDerivAt f (f' x) x) (hd' : ∀ x,HasDerivAt f' (f'' x) x)
    {M C D E : ℝ} (hM : 0≤M) (hC : 0≤C) (hD : 0≤D) (hE : 0≤E)
    (hf : ∀ x,|f x|≤C*exp (M*|x|)) (hf' : ∀ x,|f' x|≤D*exp (M*|x|))
    (hf'' : ∀ x,|f'' x|≤E*exp (M*|x|))
    (hi : Integrable (fun x => exp (M*|x|)) μ) (s : ℝ) :
    HasDerivAt (fun r => ∫ p : ℝ × ℝ,f (p.1+r*p.2) ∂μ.prod (gaussianReal 0 1))
      (s*∫ p : ℝ × ℝ,f'' (p.1+s*p.2) ∂μ.prod (gaussianReal 0 1)) s := by
  have hh := hasDerivAt_scale_prod hc hc' hd hM hC hD hf hf' hi s
  have he : (∫ p : ℝ × ℝ,p.2*f' (p.1+s*p.2) ∂μ.prod (gaussianReal 0 1))=
      s*∫ p : ℝ × ℝ,f'' (p.1+s*p.2) ∂μ.prod (gaussianReal 0 1) := by
    rw [integral_prod _ (integrable_coord_scale_prod hc' hM hD hf' hi s),
      integral_prod _ (integrable_scale_prod hc'' hM hE hf'' hi s),←integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with x
    exact scale_gaussian_ibp hc' hc'' hd' hM hD hE hf' hf'' x s
  rwa [he] at hh

def heatObservation (μ : Measure ℝ) (a : ℝ) (f : ℝ → ℝ) (t : ℝ) : ℝ :=
  ∫ p : ℝ × ℝ,f (p.1+sqrt (t-a)*p.2) ∂μ.prod (gaussianReal 0 1)

lemma hasDerivAt_heatObservation {μ : Measure ℝ} [IsFiniteMeasure μ] {f f' f'' : ℝ → ℝ}
    (hc : Continuous f) (hc' : Continuous f') (hc'' : Continuous f'')
    (hd : ∀ x,HasDerivAt f (f' x) x) (hd' : ∀ x,HasDerivAt f' (f'' x) x)
    {M C D E : ℝ} (hM : 0≤M) (hC : 0≤C) (hD : 0≤D) (hE : 0≤E)
    (hf : ∀ x,|f x|≤C*exp (M*|x|)) (hf' : ∀ x,|f' x|≤D*exp (M*|x|))
    (hf'' : ∀ x,|f'' x|≤E*exp (M*|x|))
    (hi : Integrable (fun x => exp (M*|x|)) μ) {a t : ℝ} (ht : a<t) :
    HasDerivAt (heatObservation μ a f) ((heatObservation μ a f'') t/2) t := by
  have hh := (hasDerivAt_scale_prod_second hc hc' hc'' hd hd' hM hC hD hE hf hf' hf'' hi (sqrt (t-a))).comp t
    (((hasDerivAt_id t).sub_const a).sqrt (sub_pos.mpr ht).ne')
  simp only [id_eq] at hh
  have he (I : ℝ) : (sqrt (t-a)*I)*(1/(2*sqrt (t-a)))=I/2 := by
    field_simp [(sqrt_pos.mpr (sub_pos.mpr ht)).ne']
  rw [he] at hh
  exact hh

lemma continuous_scale_prod {μ : Measure ℝ} [IsFiniteMeasure μ] {f : ℝ → ℝ}
    (hc : Continuous f) {M C : ℝ} (hM : 0≤M) (hC : 0≤C)
    (hf : ∀ x,|f x|≤C*exp (M*|x|)) (hi : Integrable (fun x => exp (M*|x|)) μ) :
    Continuous (fun s => ∫ p : ℝ × ℝ,f (p.1+s*p.2) ∂μ.prod (gaussianReal 0 1)) := by
  rw [continuous_iff_continuousAt]
  intro s
  apply continuousAt_of_dominated (bound := fun p : ℝ × ℝ => C*exp (M*|p.1|) * exp (M*(|s|+1)*|p.2|))
    (Eventually.of_forall (fun r => by fun_prop)) ?_
    ((hi.const_mul C).mul_prod (ParisiFinite.integrable_exp_abs (M*(|s|+1)))) (ae_of_all _ fun p => by fun_prop)
  filter_upwards [Metric.ball_mem_nhds s (by norm_num : (0:ℝ)<1)] with r hr
  exact ae_of_all _ fun p => by
    rw [Real.norm_eq_abs]
    exact (hf _).trans (by simpa only [mul_assoc] using (mul_le_mul_of_nonneg_left
        (exp_abs_shift_near_le hM p.1 s p.2 (by simpa [Real.dist_eq] using hr.le)) hC))

lemma continuous_heatObservation {μ : Measure ℝ} [IsFiniteMeasure μ] {f : ℝ → ℝ}
    (hc : Continuous f) {M C : ℝ} (hM : 0≤M) (hC : 0≤C)
    (hf : ∀ x,|f x|≤C*exp (M*|x|)) (hi : Integrable (fun x => exp (M*|x|)) μ) (a : ℝ) :
    Continuous (heatObservation μ a f) :=
  (continuous_scale_prod hc hM hC hf hi).comp (by fun_prop)

end ParisiSpectral

 

 

open MeasureTheory ProbabilityTheory Set Real Matrix Filter
open scoped Topology NNReal
namespace ParisiSpectral

lemma exp_neg_mul_le {L A r : ℝ} (hA : 0≤A) (hL : -A≤L) (hr : r∈Icc 0 1) :
    exp (-r*L)≤exp A := by
  apply exp_le_exp.mpr
  calc
    -r*L ≤ r*A := by nlinarith [mul_nonneg hr.1 (by linarith : 0≤L+A)]
    _ ≤ A := mul_le_of_le_one_left hA hr.2

lemma exp_neg_quotient_bound {L A r : ℝ} (hA : 0≤A) (hL : -A≤L) (hr : r∈Ioc 0 1) :
    |(exp (-r*L)-1)/r|≤exp A*|L| := by
  have hd (s : ℝ) : HasDerivAt (fun u => exp (-u*L)) (exp (-s*L)*(-L)) s := by
    convert (((hasDerivAt_id s).neg.mul_const L).exp) using 1 <;> first | rfl | (dsimp; ring)
  have hb := norm_image_sub_le_of_norm_deriv_le_segment'
    (a := 0) (b := 1) (fun s _ => (hd s).hasDerivWithinAt)
    (C := exp A*|L|) (fun s hs => by
      rw [Real.norm_eq_abs,abs_mul,abs_of_pos (exp_pos _),abs_neg]
      exact mul_le_mul_of_nonneg_right (exp_neg_mul_le hA hL ⟨hs.1,hs.2.le⟩) (abs_nonneg L)) r ⟨hr.1.le,hr.2⟩
  simp only [neg_zero,zero_mul,exp_zero,sub_zero,Real.norm_eq_abs] at hb
  rw [abs_div,abs_of_pos hr.1,div_le_iff₀ hr.1]
  exact hb

lemma integral_exp_rightDerivative {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsFiniteMeasure μ] {L g : Ω → ℝ} (hLm : AEStronglyMeasurable L μ)
    (hg : AEStronglyMeasurable g μ) {A C : ℝ} (hA : 0≤A) (hL : ∀ x,-A≤L x)
    (hC : ∀ x,|g x|≤C) (hi : Integrable (fun x => |L x|) μ) :
    Tendsto (fun r => ((∫ x,exp (-r*L x)*g x ∂μ)-∫ x,g x ∂μ)/r)
      (𝓝[>] (0:ℝ)) (𝓝 (∫ x,-L x*g x ∂μ)) := by
  have hgb : Integrable g μ := Integrable.of_bound hg C (ae_of_all _ fun x => by simpa only [Real.norm_eq_abs] using hC x)
  have hnear : ∀ᶠ r in 𝓝[>] (0:ℝ),r∈Ioc 0 1 := by
    filter_upwards [self_mem_nhdsWithin,(eventually_lt_nhds (show (0:ℝ)<1 by norm_num)).filter_mono nhdsWithin_le_nhds]
      with r hr hr1
    exact ⟨hr,hr1.le⟩
  have ht := tendsto_integral_filter_of_dominated_convergence
    (μ := μ) (l := 𝓝[>] (0:ℝ)) (bound := fun x => exp A*|L x| *C)
    (F := fun r x => ((exp (-r*L x)-1)/r)*g x) (f := fun x => -L x*g x)
    (Eventually.of_forall (fun r => ((show Continuous (fun u : ℝ => (exp (-r*u)-1)/r) from by fun_prop).comp_aestronglyMeasurable hLm).mul hg))
    (by filter_upwards [hnear] with r hr; filter_upwards [] with x
        rw [Real.norm_eq_abs,abs_mul]
        exact mul_le_mul (exp_neg_quotient_bound hA (hL x) hr) (hC x) (abs_nonneg _) (by positivity))
    ((hi.const_mul (exp A)).mul_const C)
    (ae_of_all _ fun x => by
      have hd : HasDerivAt (fun r => exp (-r*L x)) (-L x) 0 := by
        convert ((hasDerivAt_id (0:ℝ)).neg.mul_const (L x)).exp using 1 <;> first | rfl | (dsimp; simp)
      have hh := hd.tendsto_slope_zero_right.mul_const (g x)
      simpa only [zero_add,neg_zero,zero_mul,mul_zero,exp_zero,smul_eq_mul,div_eq_mul_inv,mul_comm] using hh)
  apply ht.congr'
  filter_upwards [hnear] with r hr
  have he : Integrable (fun x => exp (-r*L x)*g x) μ :=
    Integrable.of_bound ((continuous_exp.comp_aestronglyMeasurable (hLm.const_mul (-r))).mul hg) (exp A*C) (ae_of_all _ fun x => by
      rw [Real.norm_eq_abs,abs_mul,abs_of_pos (exp_pos _)]
      exact mul_le_mul (exp_neg_mul_le hA (hL x) ⟨hr.1.le,hr.2⟩) (hC x) (abs_nonneg _) (exp_pos _).le)
  have heq : (fun x => ((exp (-r*L x)-1)/r)*g x)=
      (fun x => (exp (-r*L x)*g x-g x)/r) := by funext x; ring
  rw [heq,integral_div,integral_sub he hgb]
end ParisiSpectral

 

 

open MeasureTheory ProbabilityTheory Set Real Matrix Filter
open scoped Topology NNReal
namespace ParisiSpectral

def heatLaw (μ : Measure ℝ) (a t : ℝ) : Measure ℝ := μ ∗ gaussianReal 0 (toNNReal (t-a))
instance (μ : Measure ℝ) [IsFiniteMeasure μ] (a t : ℝ) : IsFiniteMeasure (heatLaw μ a t) := by
  unfold heatLaw
  infer_instance

lemma integral_heatLaw {μ : Measure ℝ} [IsFiniteMeasure μ] {f : ℝ → ℝ} {a t : ℝ}
    (hf : Integrable f (heatLaw μ a t)) :
    (∫ x,f x ∂heatLaw μ a t)=∫ x,heat (toNNReal (t-a)) f x ∂μ := integral_conv hf

lemma heatLaw_firstMoment {μ : Measure ℝ} [IsFiniteMeasure μ]
    (hi : Integrable (fun x : ℝ => |x|) μ) (a t : ℝ) :
    Integrable (fun x : ℝ => |x|) (heatLaw μ a t) := by
  rw [heatLaw,Measure.conv,integrable_map_measure (by fun_prop) (by fun_prop)]
  have hz := ((memLp_id_gaussianReal (μ := 0) (v := toNNReal (t-a)) 1).integrable (by norm_num)).abs
  exact ((hi.comp_fst (ν := gaussianReal 0 (toNNReal (t-a)))).add
    (hz.comp_snd (μ := μ))).mono' (by fun_prop) (ae_of_all _ fun p => by
      simpa [Real.norm_eq_abs] using abs_add_le p.1 p.2)

lemma abs_log_cosh_le (x : ℝ) : |log (cosh x)|≤|x| := by
  rw [abs_of_nonneg (log_nonneg (one_le_cosh x))]
  have hc : cosh x≤exp |x| := by
    rw [cosh_eq]
    have h1 := exp_le_exp.mpr (le_abs_self x)
    have h2 := exp_le_exp.mpr (neg_le_abs x)
    linarith
  simpa only [log_exp] using log_le_log (cosh_pos x) hc

lemma backwardC_pos {K : ℝ} (hK : 0<K) (d α t x : ℝ) : 0<backwardC d K α t x := by
  unfold backwardC
  positivity

lemma backwardC_log (d K α t x : ℝ) (hK : 0<K) :
    log (backwardC d K α t x)=log K+α^2/2*(d-t)+log (cosh (α*x)) := by
  rw [backwardC,log_mul (mul_pos hK (exp_pos _)).ne' (cosh_pos _).ne',
    log_mul hK.ne' (exp_pos _).ne',log_exp]

lemma backwardC_log_integrable {μ : Measure ℝ} [IsFiniteMeasure μ]
    (hi : Integrable (fun x : ℝ => |x|) μ) {K : ℝ} (hK : 0<K) (d α t : ℝ) :
    Integrable (fun x => |log (backwardC d K α t x)|) μ := by
  have hc : Continuous (fun x => log (backwardC d K α t x)) := by
    simp only [backwardC_log d K α t _ hK]
    exact continuous_const.add ((continuous_cosh.comp (continuous_const.mul continuous_id)).log (fun x => (cosh_pos _).ne'))
  refine ((integrable_const |log K+α^2/2*(d-t)|).add (hi.const_mul |α|)).mono' hc.abs.aestronglyMeasurable ?_
  filter_upwards [] with x
  rw [Real.norm_eq_abs,abs_abs,backwardC_log d K α t x hK]
  exact (abs_add_le _ _).trans (add_le_add_right (by simpa only [abs_mul] using abs_log_cosh_le (α*x)) _)

lemma hankelPD_heatLaw {μ : Measure ℝ} [IsFiniteMeasure μ] (hμ : PositiveOnPD μ)
    {F : ℝ → ℝ → ℝ} {a : ℝ} {s : Set ℝ} (hs : ∀ t∈s,a≤t) (hsv : Convex ℝ s)
    (hc : ∀ t∈s,Continuous (F t))
    (hK : Matrix.PosSemidef (Matrix.of (fun p q : s × ℝ => F ((p.1+q.1)/2) (p.2-q.2)))) :
    HankelPD (fun t => ∫ x,F t x ∂heatLaw μ a t) s := by
  have hh := hankelPD_heat_observation hμ hs hsv hc hK
  have he (t : ℝ) (ht : t∈s) : (∫ x,F t x ∂heatLaw μ a t)=∫ x,heat (toNNReal (t-a)) (F t) x ∂μ := by
    have hb := stationary_kernel_bounded (fun u v : s => F ((u+v)/2)) hK ⟨t,ht⟩ ⟨t,ht⟩
    simp only [show (t+t)/2=t by ring] at hb
    exact integral_heatLaw (Integrable.of_bound (hc t ht).aestronglyMeasurable _ (ae_of_all _ hb))
  have hm (x y : s) : ((x:ℝ)+y)/2∈s := by
    simpa only [midpoint_eq_smul_add,smul_eq_mul,invOf_eq_inv,div_eq_mul_inv,mul_comm] using hsv.midpoint_mem x.property y.property
  change (Matrix.of (fun x y : s => ∫ z,F ((x+y)/2) z ∂heatLaw μ a ((x+y)/2))).PosSemidef
  change (Matrix.of (fun x y : s => ∫ z,heat (toNNReal (((x:ℝ)+y)/2-a)) (F ((x+y)/2)) z ∂μ)).PosSemidef at hh
  simpa only [he _ (hm _ _)] using hh

lemma backwardG_observation_constant {μ : Measure ℝ} [IsFiniteMeasure μ]
    {g : ℝ → ℝ} (hg : PositiveDefinite g) (hc : Continuous g) {a d t : ℝ}
    (hat : a≤t) (htd : t≤d) :
    (∫ x,backwardG d g t x ∂heatLaw μ a t)=∫ x,heat (toNNReal (d-a)) g x ∂μ := by
  have hh := integral_heatLaw (μ := μ) (a := a) (t := t)
    (Integrable.of_bound (continuous_heat hc hg.norm_le _).aestronglyMeasurable _
      (ae_of_all _ fun x => by simpa only [Real.norm_eq_abs] using hg.heat_abs_le hc (toNNReal (d-t)) x))
  rw [heat_heat hc hg.norm_le] at hh
  have he : toNNReal (t-a)+toNNReal (d-t)=toNNReal (d-a) := by
    apply NNReal.eq
    rw [NNReal.coe_add,coe_toNNReal _ (sub_nonneg.mpr hat),coe_toNNReal _ (sub_nonneg.mpr htd),
      coe_toNNReal _ (sub_nonneg.mpr (hat.trans htd))]
    ring
  simpa only [backwardG,he] using hh

lemma backwardG_bound {g : ℝ → ℝ} (hg : PositiveDefinite g) (hc : Continuous g)
    (d t x : ℝ) : |backwardG d g t x|≤g 0 := hg.heat_abs_le hc _ _

lemma hankelCPD_linearEntropy {μ : Measure ℝ} [IsFiniteMeasure μ]
    (hμ : PositiveOnPD μ) (hi : Integrable (fun x : ℝ => |x|) μ)
    {g : ℝ → ℝ} (hg : PositiveDefinite g) (hc : Continuous g)
    {a d K α : ℝ} (hK : 0<K) {s : Set ℝ}
    (hs : ∀ t∈s,a≤t ∧ t≤d) (hsv : Convex ℝ s) :
    HankelCPD (fun t => ∫ x,-log (backwardC d K α t x)*backwardG d g t x ∂heatLaw μ a t) s := by
  let F (r t : ℝ) := ∫ x,(backwardC d K α t x)^(-r)*backwardG d g t x ∂heatLaw μ a t
  apply HankelCPD.of_rightQuotient (F := F) (C := ∫ x,heat (toNNReal (d-a)) g x ∂μ) hsv
  · intro r hr
    apply hankelPD_heatLaw hμ (fun t ht => (hs t ht).1) hsv
    · intro t ht
      have hcc : Continuous (backwardC d K α t) := by unfold backwardC; fun_prop
      exact (hcc.rpow_const (fun x => Or.inl (backwardC_pos hK _ _ _ x).ne')).mul (continuous_heat hc hg.norm_le _)
    · exact (backwardC_neg_rpow hK hr s).hadamard (backwardG_reflection hg hc (fun t ht => (hs t ht).2))
  · intro t ht
    let L : ℝ → ℝ := fun x => log (backwardC d K α t x)
    have hLc : Continuous L := by
      unfold L
      simp only [backwardC_log d K α t _ hK]
      exact continuous_const.add ((continuous_cosh.comp (continuous_const.mul continuous_id)).log (fun x => (cosh_pos _).ne'))
    have hL (x : ℝ) : -|log K+α^2/2*(d-t)|≤L x := by
      dsimp only [L]
      rw [backwardC_log d K α t x hK]
      have := log_nonneg (one_le_cosh (α*x))
      linarith [neg_abs_le (log K+α^2/2*(d-t))]
    have hh := integral_exp_rightDerivative hLc.aestronglyMeasurable
      (continuous_heat hc hg.norm_le (toNNReal (d-t))).aestronglyMeasurable
      (abs_nonneg (log K+α^2/2*(d-t))) hL (backwardG_bound hg hc d t)
      (backwardC_log_integrable (heatLaw_firstMoment hi a t) hK d α t)
    change Tendsto (fun r => ((∫ x,exp (-r*L x)*backwardG d g t x ∂heatLaw μ a t)-∫ x,backwardG d g t x ∂heatLaw μ a t)/r) (𝓝[>] (0:ℝ)) (𝓝 (∫ x,-L x*backwardG d g t x ∂heatLaw μ a t)) at hh
    rw [backwardG_observation_constant hg hc (hs t ht).1 (hs t ht).2] at hh
    apply hh.congr
    intro r
    dsimp only [F]
    congr 2
    apply integral_congr_ae
    filter_upwards [] with x
    simp only [rpow_def_of_pos (backwardC_pos hK _ _ _ _),L,mul_comm]

lemma hankelPD_entropyRemainder {μ : Measure ℝ} [IsFiniteMeasure μ]
    (hμ : PositiveOnPD μ) {g : ℝ → ℝ} (hg : PositiveDefinite g) (hc : Continuous g)
    {a d K α : ℝ} (hK : 0<K) (hgK : g 0<K) {s : Set ℝ}
    (hs : ∀ t∈s,a≤t ∧ t≤d) (hsv : Convex ℝ s) :
    HankelPD (fun t => ∫ x,
      (backwardC d K α t x-backwardG d g t x)*log (backwardC d K α t x-backwardG d g t x)-
      backwardC d K α t x*log (backwardC d K α t x)+
      (1+log (backwardC d K α t x))*backwardG d g t x ∂heatLaw μ a t) s := by
  have hcb (t : ℝ) (ht : t≤d) (x : ℝ) : K≤backwardC d K α t x := by
    unfold backwardC
    have he : 1≤exp (α^2/2*(d-t)) := one_le_exp_iff.mpr (by positivity)
    have hh : K≤K*exp (α^2/2*(d-t)) := by simpa only [mul_one] using mul_le_mul_of_nonneg_left he hK.le
    exact hh.trans (le_mul_of_one_le_right (mul_pos hK (exp_pos _)).le (one_le_cosh _))
  have hd (t : ℝ) (ht : t≤d) (x : ℝ) : |backwardG d g t x|<backwardC d K α t x :=
    (backwardG_bound hg hc d t x).trans_lt (hgK.trans_le (hcb t ht x))
  apply hankelPD_heatLaw hμ (fun t ht => (hs t ht).1) hsv
  · intro t ht
    have hCc : Continuous (backwardC d K α t) := by unfold backwardC; fun_prop
    have hGc := continuous_heat hc hg.norm_le (toNNReal (d-t))
    have hdc : Continuous (fun x => backwardC d K α t x-backwardG d g t x) := hCc.sub hGc
    have hdp (x : ℝ) : 0<backwardC d K α t x-backwardG d g t x := by
      have := hd t (hs t ht).2 x
      linarith [le_abs_self (backwardG d g t x)]
    exact ((hdc.mul (hdc.log (fun x => (hdp x).ne'))).sub
      (hCc.mul (hCc.log (fun x => (backwardC_pos hK _ _ _ x).ne')))).add
      ((continuous_const.add (hCc.log (fun x => (backwardC_pos hK _ _ _ x).ne'))).mul hGc)
  · apply posSemidef_entropy_remainder
    · intro p q
      exact backwardC_pos hK _ _ _ _
    · exact backwardG_reflection hg hc (fun t ht => (hs t ht).2)
    · intro p q
      exact hd _ (by linarith [(hs p.1 p.1.property).2,(hs q.1 q.1.property).2]) _
    · intro n
      exact backwardC_neg_rpow hK (by positivity) s

end ParisiSpectral

end

end OAI
