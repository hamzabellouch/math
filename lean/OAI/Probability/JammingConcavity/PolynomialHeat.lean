import Mathlib
import OAI.Probability.JammingConcavity.GaussianTwiceTerminal

namespace OAI

/-! Polynomial Heat. -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
open Set Filter
open scoped Topology
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory Filter Set
open scoped ENNReal NNReal BigOperators
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
open scoped NNReal ENNReal Topology
open scoped NNReal Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology

namespace MicroscopicJamming
namespace Higher

def PolynomialGrowth (v : ℝ → ℝ) : Prop :=
  ∃ n : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ x, |v x| ≤ C*(1+|x|)^n

lemma PolynomialGrowth.of_bound {v : ℝ → ℝ} {C : ℝ} (hv : ∀ x, |v x| ≤ C) :
    PolynomialGrowth v :=
  ⟨0,C,(abs_nonneg (v 0)).trans (hv 0),by simpa using hv⟩

lemma PolynomialGrowth.of_quadratic {v : ℝ → ℝ} (hv : HeatQuadraticGrowth v) :
    PolynomialGrowth v := by
  obtain ⟨C,hC,hv⟩ := hv
  exact ⟨2,C,hC,hv⟩

lemma PolynomialGrowth.const (c : ℝ) : PolynomialGrowth (fun _ : ℝ => c) :=
  .of_bound (C:=|c|) (fun _ => le_rfl)

lemma PolynomialGrowth.add {f g : ℝ → ℝ} (hf : PolynomialGrowth f)
    (hg : PolynomialGrowth g) : PolynomialGrowth (fun x => f x+g x) := by
  obtain ⟨n,C,hC,hf⟩ := hf
  obtain ⟨m,D,hD,hg⟩ := hg
  refine ⟨max n m,C+D,add_nonneg hC hD,fun x => ?_⟩
  calc
    |f x+g x| ≤ |f x|+|g x| := abs_add_le _ _
    _ ≤ C*(1+|x|)^n+D*(1+|x|)^m := add_le_add (hf x) (hg x)
    _ ≤ C*(1+|x|)^(max n m)+D*(1+|x|)^(max n m) := add_le_add
      (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by linarith [abs_nonneg x]) (le_max_left ..)) hC)
      (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by linarith [abs_nonneg x]) (le_max_right ..)) hD)
    _ = _ := by ring

lemma PolynomialGrowth.mul {f g : ℝ → ℝ} (hf : PolynomialGrowth f)
    (hg : PolynomialGrowth g) : PolynomialGrowth (fun x => f x*g x) := by
  obtain ⟨n,C,hC,hf⟩ := hf
  obtain ⟨m,D,hD,hg⟩ := hg
  refine ⟨n+m,C*D,mul_nonneg hC hD,fun x => ?_⟩
  rw [abs_mul]
  calc
    |f x| * |g x| ≤ (C*(1+|x|)^n)*(D*(1+|x|)^m) :=
      mul_le_mul (hf x) (hg x) (abs_nonneg _) (by positivity)
    _ = _ := by rw [pow_add]; ring

lemma PolynomialGrowth.finset_sum {ι : Type*} (s : Finset ι) {f : ι → ℝ → ℝ}
    (hf : ∀ i ∈ s, PolynomialGrowth (f i)) : PolynomialGrowth (fun x => ∑ i ∈ s, f i x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using PolynomialGrowth.const 0
  | @insert a s ha ih =>
      simpa [Finset.sum_insert,ha] using (hf a (by simp)).add (ih (fun i hi => hf i (by simp [hi])))

lemma affine_integrable {v : ℝ → ℝ} (hv : Measurable v)
    (hg : PolynomialGrowth v) (a b : ℝ) :
    Integrable (fun z : ℝ => v (a+b*z)) (gaussianReal 0 1) := by
  obtain ⟨n,C,hC,hg⟩ := hg
  have hdom := (gaussian_abs_one_pow_integrable n).const_mul (C*(1+|a|+|b|)^n)
  apply hdom.mono' (hv.comp (by fun_prop)).aestronglyMeasurable
  filter_upwards [] with z
  rw [Real.norm_eq_abs]
  calc
    |v (a+b*z)| ≤ C*(1+|a+b*z|)^n := hg _
    _ ≤ C*((1+|a|+|b|)*(1+|z|))^n :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) (heat_affine_bound a b z) n) hC
    _ = C*(1+|a|+|b|)^n*(1+|z|)^n := by rw [mul_pow]; ring

lemma affine_mul_integrable {v : ℝ → ℝ} (hv : Measurable v)
    (hg : PolynomialGrowth v) (a b : ℝ) :
    Integrable (fun z : ℝ => z*v (a+b*z)) (gaussianReal 0 1) := by
  obtain ⟨n,C,hC,hg⟩ := hg
  apply ((gaussian_abs_one_pow_integrable (n+1)).const_mul (C*(1+|a|+|b|)^n)).mono'
    (measurable_id.mul (hv.comp (by fun_prop))).aestronglyMeasurable
  filter_upwards [] with z
  change |z*v (a+b*z)| ≤ _
  rw [abs_mul]
  have ht := pow_le_pow_left₀ (by positivity : 0 ≤ 1+|a+b*z|) (heat_affine_bound a b z) n
  calc
    |z| *|v (a+b*z)| ≤ (1+|z|)*(C*((1+|a|+|b|)*(1+|z|))^n) :=
      mul_le_mul (by linarith) ((hg _).trans (mul_le_mul_of_nonneg_left ht hC)) (abs_nonneg _) (by positivity)
    _ = C*(1+|a|+|b|)^n*(1+|z|)^(n+1) := by rw [mul_pow,pow_succ]; ring

lemma curve_derivative {v v' : ℝ → ℝ} (hv : Measurable v) (hv' : Measurable v')
    (hg : PolynomialGrowth v) (hg' : PolynomialGrowth v')
    (hdv : ∀ x, HasDerivAt v (v' x) x)
    {a b a' b' : ℝ → ℝ} {t₀ : ℝ} {s : Set ℝ} (hs : s ∈ 𝓝 t₀)
    (hda : ∀ t ∈ s, HasDerivAt a (a' t) t)
    (hdb : ∀ t ∈ s, HasDerivAt b (b' t) t)
    (hca' : ContinuousAt a' t₀) (hcb' : ContinuousAt b' t₀) :
    HasDerivAt (fun t => ∫ z : ℝ, v (a t+b t*z) ∂gaussianReal 0 1)
      (∫ z : ℝ, v' (a t₀+b t₀*z)*(a' t₀+b' t₀*z) ∂gaussianReal 0 1) t₀ := by
  let K := 1+|a t₀|+|b t₀|+|a' t₀|+|b' t₀|
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have h0 := mem_of_mem_nhds hs
  have hAb : |a t₀| < K := by dsimp [K]; linarith [abs_nonneg (b t₀), abs_nonneg (a' t₀), abs_nonneg (b' t₀)]
  have hBb : |b t₀| < K := by dsimp [K]; linarith [abs_nonneg (a t₀), abs_nonneg (a' t₀), abs_nonneg (b' t₀)]
  have hAd : |a' t₀| < K := by dsimp [K]; linarith [abs_nonneg (a t₀), abs_nonneg (b t₀), abs_nonneg (b' t₀)]
  have hBd : |b' t₀| < K := by dsimp [K]; linarith [abs_nonneg (a t₀), abs_nonneg (b t₀), abs_nonneg (a' t₀)]
  have hea : ∀ᶠ t in 𝓝 t₀, |a t| ≤ K :=
    (((hda t₀ h0).continuousAt.abs.tendsto).eventually (eventually_lt_nhds hAb)).mono fun _ h => h.le
  have heb : ∀ᶠ t in 𝓝 t₀, |b t| ≤ K :=
    (((hdb t₀ h0).continuousAt.abs.tendsto).eventually (eventually_lt_nhds hBb)).mono fun _ h => h.le
  have hea' : ∀ᶠ t in 𝓝 t₀, |a' t| ≤ K :=
    (hca'.abs.tendsto.eventually (eventually_lt_nhds hAd)).mono fun _ h => h.le
  have heb' : ∀ᶠ t in 𝓝 t₀, |b' t| ≤ K :=
    (hcb'.abs.tendsto.eventually (eventually_lt_nhds hBd)).mono fun _ h => h.le
  obtain ⟨n,C,hC,hgrow⟩ := hg'
  let U := {t | t ∈ s ∧ |a t| ≤ K ∧ |b t| ≤ K ∧ |a' t| ≤ K ∧ |b' t| ≤ K}
  have hU : U ∈ 𝓝 t₀ := inter_mem hs (hea.and (heb.and (hea'.and heb')))
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := gaussianReal 0 1) (s := U) (F := fun t z => v (a t+b t*z))
    (F' := fun t z => v' (a t+b t*z)*(a' t+b' t*z))
    (bound := fun z => C*(1+2*K)^n*K*(1+|z|)^(n+1)) hU
    (Eventually.of_forall fun t => (hv.comp (by fun_prop)).aestronglyMeasurable)
    (affine_integrable hv hg (a t₀) (b t₀))
    (((hv'.comp (by fun_prop)).mul (by fun_prop)).aestronglyMeasurable)
    ?_ ((gaussian_abs_one_pow_integrable (n+1)).const_mul _) ?_).2
  · filter_upwards [] with z
    intro t ht
    have hab : 1+|a t+b t*z| ≤ (1+2*K)*(1+|z|) := by
      have h := heat_affine_bound (a t) (b t) z
      have hp := mul_le_mul_of_nonneg_right (show 1+|a t|+|b t| ≤ 1+2*K by linarith [ht.2.1,ht.2.2.1])
        (show 0 ≤ 1+|z| by positivity)
      exact h.trans hp
    have hd : |a' t+b' t*z| ≤ K*(1+|z|) := by
      have h := abs_add_le (a' t) (b' t*z)
      rw [abs_mul] at h
      have hp := mul_le_mul_of_nonneg_right ht.2.2.2.2 (abs_nonneg z)
      nlinarith [ht.2.2.2.1]
    rw [Real.norm_eq_abs, abs_mul]
    calc
      |v' (a t+b t*z)| * |a' t+b' t*z| ≤
          (C*((1+2*K)*(1+|z|))^n)*(K*(1+|z|)) :=
        mul_le_mul ((hgrow _).trans (mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (by positivity) hab n) hC)) hd (abs_nonneg _) (by positivity)
      _ = C*(1+2*K)^n*K*(1+|z|)^(n+1) := by rw [mul_pow,pow_succ]; ring
  · filter_upwards [] with z
    intro t ht
    exact (hdv _).comp t ((hda t ht.1).add ((hdb t ht.1).mul_const z))

lemma space_derivative {v v' : ℝ → ℝ}
    (hv : Measurable v) (hv' : Measurable v')
    (hg : PolynomialGrowth v) (hg' : PolynomialGrowth v')
    (hdv : ∀ x, HasDerivAt v (v' x) x) (T x : ℝ) :
    HasDerivAt (gaussianHeat v T) (gaussianHeat v' T x) x := by
  have hh := curve_derivative hv hv' hg hg' hdv
    (a := id) (b := fun _ => Real.sqrt T) (a' := fun _ => 1) (b' := fun _ => 0)
    (t₀ := x) (s := univ) univ_mem
    (fun t _ => hasDerivAt_id t) (fun t _ => hasDerivAt_const t _)
    continuousAt_const continuousAt_const
  convert hh using 1 <;> first | rfl | simp only [gaussianHeat, id_eq, zero_mul, add_zero, mul_one]

lemma time_derivative {v v' v'' : ℝ → ℝ}
    (hv : Measurable v) (hv' : Measurable v') (hv'' : Measurable v'')
    (hg : PolynomialGrowth v) (hg' : PolynomialGrowth v') (hg'' : PolynomialGrowth v'')
    (hdv : ∀ x, HasDerivAt v (v' x) x) (hdv' : ∀ x, HasDerivAt v' (v'' x) x)
    {T : ℝ} (hT : 0 < T) (x : ℝ) :
    HasDerivAt (fun r => gaussianHeat v r x) ((1/2:ℝ)*gaussianHeat v'' T x) T := by
  have hs : Ioi (0:ℝ) ∈ 𝓝 T := Ioi_mem_nhds hT
  have hc : ContinuousAt (fun t : ℝ => (2*Real.sqrt t)⁻¹) T :=
    (continuousAt_const.mul (Real.continuous_sqrt.continuousAt)).inv₀ (mul_ne_zero (by norm_num) (Real.sqrt_ne_zero'.mpr hT))
  have hh := curve_derivative hv hv' hg hg' hdv
    (a := fun _ => x) (b := Real.sqrt) (a' := fun _ => 0) (b' := fun t => (2*Real.sqrt t)⁻¹)
    hs (fun t _ => hasDerivAt_const t _) (fun t ht => by simpa only [one_div] using Real.hasDerivAt_sqrt (show t ≠ 0 from ht.ne'))
    continuousAt_const hc
  have hi := standardGaussian_integration_by_parts
    (f := fun z => v' (x+Real.sqrt T*z))
    (f' := fun z => v'' (x+Real.sqrt T*z)*Real.sqrt T)
    (fun z => by
      convert (hdv' _).comp z ((hasDerivAt_const z x).add
        ((hasDerivAt_id z).const_mul (Real.sqrt T))) using 1 <;> first | rfl | simp)
    (affine_integrable hv' hg' x (Real.sqrt T))
    ((affine_integrable hv'' hg'' x (Real.sqrt T)).mul_const _)
    (affine_mul_integrable hv' hg' x (Real.sqrt T))
  have he : (∫ z : ℝ, v' (x+Real.sqrt T*z)*(0+(2*Real.sqrt T)⁻¹*z) ∂gaussianReal 0 1) =
      (1/2:ℝ)*gaussianHeat v'' T x := by
    calc
      _ = (2*Real.sqrt T)⁻¹*(∫ z : ℝ, z*v' (x+Real.sqrt T*z) ∂gaussianReal 0 1) := by
        rw [← integral_const_mul]; congr 1; funext z; ring
      _ = (2*Real.sqrt T)⁻¹*((∫ z : ℝ, v'' (x+Real.sqrt T*z) ∂gaussianReal 0 1)*Real.sqrt T) := by
        rw [hi, integral_mul_const]
      _ = (1/2:ℝ)*gaussianHeat v'' T x := by
        dsimp [gaussianHeat]; field_simp [Real.sqrt_ne_zero'.mpr hT]
  rw [he] at hh
  exact hh

end Higher
end MicroscopicJamming

 
 

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology

namespace MicroscopicJamming
namespace Higher

lemma PolynomialGrowth.id : PolynomialGrowth (fun x : ℝ => x) :=
  ⟨1,1,by norm_num,fun x => by simp⟩

lemma PolynomialGrowth.pow {f : ℝ → ℝ} (hf : PolynomialGrowth f) (n : ℕ) :
    PolynomialGrowth (fun x => (f x)^n) := by
  induction n with
  | zero => simpa using PolynomialGrowth.const 1
  | succ n ih => simpa only [pow_succ] using ih.mul hf

lemma PolynomialGrowth.affine {f : ℝ → ℝ} (hf : PolynomialGrowth f) (a b : ℝ) :
    PolynomialGrowth (fun z => f (a+b*z)) := by
  obtain ⟨n,C,hC,hf⟩ := hf
  refine ⟨n,C*(1+|a|+|b|)^n,by positivity,fun z => ?_⟩
  calc
    |f (a+b*z)| ≤ C*(1+|a+b*z|)^n := hf _
    _ ≤ C*((1+|a|+|b|)*(1+|z|))^n :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) (heat_affine_bound a b z) n) hC
    _ = _ := by rw [mul_pow]; ring

lemma weighted_poly_integrable {u f : ℝ → ℝ} {B a x b : ℝ}
    (hu : Continuous u) (hb : ∀ y, u y ≤ B) (ha : 0 ≤ a)
    (hf : Measurable f) (hg : PolynomialGrowth f) :
    Integrable (fun z => f z*Real.exp (a*u (x+b*z))) (gaussianReal 0 1) := by
  obtain ⟨n,C,hC,hg⟩ := hg
  apply gaussian_weighted_poly_integrable hf (by fun_prop) hC (Real.exp_pos (a*B)).le n hg
  intro z
  rw [abs_of_pos (Real.exp_pos _)]
  exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (hb _) ha)

lemma tilted_even_stein {u : ℝ → ℝ} {A B C κ Q a x b : ℝ}
    (hu : Twice.RowTwiceTerminal u A B C κ Q) (ha : 0 ≤ a) (n : ℕ) :
    (∫ z : ℝ,z^(2*n+2)*Real.exp (a*u (x+b*z)) ∂gaussianReal 0 1) =
      (2*(n:ℝ)+1)*(∫ z : ℝ,z^(2*n)*Real.exp (a*u (x+b*z)) ∂gaussianReal 0 1)+
      a*b*(∫ z : ℝ,z^(2*n+1)*deriv u (x+b*z)*Real.exp (a*u (x+b*z)) ∂gaussianReal 0 1) := by
  let w := fun z => Real.exp (a*u (x+b*z))
  have hw (z : ℝ) : HasDerivAt w (a*b*(deriv u (x+b*z)*w z)) z := by
    have hz : HasDerivAt (fun r : ℝ => x+b*r) b z := by
      convert (hasDerivAt_const z x).add ((hasDerivAt_id z).const_mul b) using 1 <;> first | rfl | simp
    convert (((hu.differentiable _).hasDerivAt.comp z hz).const_mul a).exp using 1 <;>
      first | rfl | (dsimp [w]; ring)
  have hd (z : ℝ) : HasDerivAt (fun r => r^(2*n+1)*w r)
      ((2*(n:ℝ)+1)*(z^(2*n)*w z)+a*b*(z^(2*n+1)*deriv u (x+b*z)*w z)) z := by
    convert ((hasDerivAt_id z).pow (2*n+1)).mul (hw z) using 1 <;> first | rfl | (simp; ring)
  have hi (k : ℕ) : Integrable (fun z : ℝ => z^k*w z) (gaussianReal 0 1) :=
    weighted_poly_integrable hu.differentiable.continuous (fun y => (hu.bounds y).2.1) ha
      (by fun_prop) (PolynomialGrowth.id.pow k)
  have his : Integrable (fun z : ℝ => z^(2*n+1)*deriv u (x+b*z)*w z) (gaussianReal 0 1) :=
    weighted_poly_integrable hu.differentiable.continuous (fun y => (hu.bounds y).2.1) ha
      (by fun_prop) ((PolynomialGrowth.id.pow (2*n+1)).mul
        ((PolynomialGrowth.of_quadratic (Twice.row_terminal_deriv_growth hu)).affine x b))
  have hzi : Integrable (fun z : ℝ => z*(z^(2*n+1)*w z)) (gaussianReal 0 1) := by
    convert hi (2*n+2) using 1
    funext z
    rw [show 2*n+2=(2*n+1)+1 by omega,pow_succ]
    ring
  have hh := standardGaussian_integration_by_parts hd (hi (2*n+1))
    (((hi (2*n)).const_mul (2*(n:ℝ)+1)).add (his.const_mul (a*b))) hzi
  rw [integral_add ((hi (2*n)).const_mul (2*(n:ℝ)+1)) (his.const_mul (a*b)),
    integral_const_mul,integral_const_mul] at hh
  convert hh using 1
  congr 1; funext z
  rw [show 2*n+2=(2*n+1)+1 by omega,pow_succ]
  ring

lemma tilted_slope_bound {u : ℝ → ℝ} {A B C κ Q : ℝ}
    (hu : Twice.RowTwiceTerminal u A B C κ Q) (x : ℝ) {b : ℝ} (hb : 0 ≤ b) (z : ℝ) :
    z*deriv u (x+b*z) ≤ z*deriv u x+κ*b*z^2 := by
  have hm := Twice.row_slope_antitone hu x hb
  by_cases hz : 0 ≤ z
  · have hh := mul_le_mul_of_nonneg_left (hm hz) hz
    simp only [mul_zero,add_zero,sub_zero] at hh
    nlinarith
  · have hh := mul_le_mul_of_nonpos_left (hm (le_of_lt (lt_of_not_ge hz))) (le_of_lt (lt_of_not_ge hz))
    simp only [mul_zero,add_zero,sub_zero] at hh
    nlinarith

lemma tilted_even_recurrence {u : ℝ → ℝ} {A B C κ Q a x b δ : ℝ}
    (hu : Twice.RowTwiceTerminal u A B C κ Q) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hδ : 0 < δ) (hden : δ ≤ 1-a*κ*b^2) (n : ℕ) :
    (∫ z : ℝ,z^(2*(n+1))*Real.exp (a*u (x+b*z)) ∂gaussianReal 0 1) ≤
      (2/δ*(2*(n:ℝ)+1+(a*b*deriv u x)^2/(2*δ)))*
        (∫ z : ℝ,z^(2*n)*Real.exp (a*u (x+b*z)) ∂gaussianReal 0 1) := by
  let w := fun z => Real.exp (a*u (x+b*z))
  let D := a*b*deriv u x
  let J := fun k : ℕ => ∫ z : ℝ,z^k*w z ∂gaussianReal 0 1
  have hi (k : ℕ) : Integrable (fun z : ℝ => z^k*w z) (gaussianReal 0 1) :=
    weighted_poly_integrable hu.differentiable.continuous (fun y => (hu.bounds y).2.1) ha
      (by fun_prop) (PolynomialGrowth.id.pow k)
  have his : Integrable (fun z : ℝ => z^(2*n+1)*deriv u (x+b*z)*w z) (gaussianReal 0 1) :=
    weighted_poly_integrable hu.differentiable.continuous (fun y => (hu.bounds y).2.1) ha
      (by fun_prop) ((PolynomialGrowth.id.pow (2*n+1)).mul
        ((PolynomialGrowth.of_quadratic (Twice.row_terminal_deriv_growth hu)).affine x b))
  have hbnd (z : ℝ) :
      (2*(n:ℝ)+1)*z^(2*n)+a*b*(z^(2*n+1)*deriv u (x+b*z)) ≤
        (1-δ/2)*z^(2*n+2)+(2*(n:ℝ)+1+D^2/(2*δ))*z^(2*n) := by
    have hy0 : (D*z-δ/2*z^2)*(2*δ) ≤ D^2 := by nlinarith [sq_nonneg (δ*z-D)]
    have hy : D*z ≤ δ/2*z^2+D^2/(2*δ) := by
      have hh := (le_div_iff₀ (show 0 < 2*δ by positivity)).mpr hy0
      linarith
    have hs := mul_le_mul_of_nonneg_left (tilted_slope_bound hu x hb z) (mul_nonneg ha hb)
    have hz : 0 ≤ z^(2*n) := by rw [pow_mul]; positivity
    have hdenz := mul_le_mul_of_nonneg_right hden (sq_nonneg z)
    have ha' : a*b*(z*deriv u (x+b*z)) ≤ (1-δ/2)*z^2+D^2/(2*δ) := by
      dsimp [D] at hy
      nlinarith
    have hh := mul_le_mul_of_nonneg_right ha' hz
    rw [show z^(2*n+1)=z^(2*n)*z by rw [pow_succ],
      show z^(2*n+2)=z^(2*n)*z^2 by rw [pow_add]]
    nlinarith only [hh]
  have him := integral_mono
    (((hi (2*n)).const_mul (2*(n:ℝ)+1)).add (his.const_mul (a*b)))
    (((hi (2*n+2)).const_mul (1-δ/2)).add ((hi (2*n)).const_mul (2*(n:ℝ)+1+D^2/(2*δ))))
    (fun z => by
      convert mul_le_mul_of_nonneg_right (hbnd z) (Real.exp_pos (a*u (x+b*z))).le using 1 <;>
        dsimp [w] <;> ring)
  simp only [Pi.add_apply] at him
  rw [integral_add ((hi (2*n)).const_mul (2*(n:ℝ)+1)) (his.const_mul (a*b)),
    integral_add ((hi (2*n+2)).const_mul (1-δ/2)) ((hi (2*n)).const_mul (2*(n:ℝ)+1+D^2/(2*δ))),
    integral_const_mul,integral_const_mul,integral_const_mul,integral_const_mul] at him
  have hs := tilted_even_stein (x:=x) (b:=b) hu ha n
  change J (2*n+2)=(2*(n:ℝ)+1)*J (2*n)+a*b*_ at hs
  change (2*(n:ℝ)+1)*J (2*n)+a*b*_ ≤ (1-δ/2)*J (2*n+2)+(2*(n:ℝ)+1+D^2/(2*δ))*J (2*n) at him
  rw [←hs] at him
  have hprod : (δ/2)*J (2*n+2) ≤ (2*(n:ℝ)+1+D^2/(2*δ))*J (2*n) := by linarith
  have hh : J (2*n+2) ≤ ((2*(n:ℝ)+1+D^2/(2*δ))*J (2*n))/(δ/2) :=
    (le_div_iff₀ (show 0 < δ/2 by positivity)).mpr (by linarith only [hprod])
  change J (2*(n+1)) ≤ _
  rw [show 2*(n+1)=2*n+2 by omega]
  convert hh using 1
  dsimp [D,J,w]
  ring

lemma tilted_even_moment_bound {u : ℝ → ℝ} {A B C κ Q a R δ : ℝ}
    (hu : Twice.RowTwiceTerminal u A B C κ Q) (ha : 0 ≤ a) (hR : 0 ≤ R)
    (hδ : 0 < δ) (hden : δ ≤ 1-a*κ*R^2) (n : ℕ) :
    ∃ H : ℝ, 0 ≤ H ∧ ∀ b : ℝ, 0 ≤ b → b ≤ R → ∀ x : ℝ,
      (∫ z : ℝ,z^(2*n)*Real.exp (a*u (x+b*z)) ∂gaussianReal 0 1) ≤
        H*(1+|x|)^(2*n)*(∫ z : ℝ,Real.exp (a*u (x+b*z)) ∂gaussianReal 0 1) := by
  obtain ⟨L,hL,hlin⟩ := Twice.row_terminal_deriv_linear hu
  induction n with
  | zero => exact ⟨1,by norm_num,by simp⟩
  | succ n ih =>
    obtain ⟨H,hH,hbnd⟩ := ih
    let K := 2/δ*(2*(n:ℝ)+1+(a*R*L)^2/(2*δ))
    have hK : 0 ≤ K := by dsimp [K]; positivity
    refine ⟨K*H,mul_nonneg hK hH,?_⟩
    intro b hb hbR x
    have hdenb : δ ≤ 1-a*κ*b^2 := by
      have hs := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hb hbR 2)
        (mul_nonneg ha hu.kappa_nonneg)
      nlinarith
    have hJ : 0 ≤ ∫ z : ℝ,z^(2*n)*Real.exp (a*u (x+b*z)) ∂gaussianReal 0 1 :=
      integral_nonneg (fun z => mul_nonneg (by rw [pow_mul]; positivity) (Real.exp_pos _).le)
    have hZ : 0 ≤ ∫ z : ℝ,Real.exp (a*u (x+b*z)) ∂gaussianReal 0 1 :=
      integral_nonneg (fun z => (Real.exp_pos _).le)
    have hD : |a*b*deriv u x| ≤ a*R*L*(1+|x|) := by
      rw [abs_mul,abs_of_nonneg (mul_nonneg ha hb)]
      calc
        a*b*|deriv u x| ≤ (a*R)*(L*(1+|x|)) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hbR ha) (hlin x) (abs_nonneg _) (mul_nonneg ha hR)
        _ = _ := by ring
    have hDs : (a*b*deriv u x)^2 ≤ (a*R*L)^2*(1+|x|)^2 := by
      have hs := pow_le_pow_left₀ (abs_nonneg _) hD 2
      simpa only [sq_abs,mul_pow] using hs
    have hbase : (1:ℝ) ≤ (1+|x|)^2 := by nlinarith [abs_nonneg x,sq_nonneg x,sq_abs x]
    have hcoef : 2/δ*(2*(n:ℝ)+1+(a*b*deriv u x)^2/(2*δ)) ≤ K*(1+|x|)^2 := by
      have hs := div_le_div_of_nonneg_right hDs (by positivity : 0 ≤ 2*δ)
      have hh := mul_le_mul_of_nonneg_left hbase (show 0 ≤ 2*(n:ℝ)+1 by positivity)
      apply (mul_le_mul_of_nonneg_left (show
        2*(n:ℝ)+1+(a*b*deriv u x)^2/(2*δ) ≤
          (2*(n:ℝ)+1+(a*R*L)^2/(2*δ))*(1+|x|)^2 by
          convert add_le_add hh hs using 1 <;> ring) (show 0 ≤ 2/δ by positivity)).trans_eq
      dsimp [K]; ring
    calc
      _ ≤ (2/δ*(2*(n:ℝ)+1+(a*b*deriv u x)^2/(2*δ)))*
        (∫ z : ℝ,z^(2*n)*Real.exp (a*u (x+b*z)) ∂gaussianReal 0 1) :=
        tilted_even_recurrence hu ha hb hδ hdenb n
      _ ≤ (K*(1+|x|)^2)*(H*(1+|x|)^(2*n)*
        (∫ z : ℝ,Real.exp (a*u (x+b*z)) ∂gaussianReal 0 1)) :=
        mul_le_mul hcoef (hbnd b hb hbR x) hJ (by positivity)
      _ = _ := by rw [show 2*(n+1)=2*n+2 by omega,pow_add]; ring

lemma one_abs_pow_le_even (n : ℕ) (z : ℝ) :
    (1+|z|)^n ≤ (2:ℝ)^n*(1+z^(2*n)) := by
  have hz : 0 ≤ z^(2*n) := by rw [pow_mul]; positivity
  by_cases h : |z| ≤ 1
  · calc
      (1+|z|)^n ≤ (2:ℝ)^n := pow_le_pow_left₀ (by positivity) (by linarith) n
      _ ≤ (2:ℝ)^n*(1+z^(2*n)) := le_mul_of_one_le_right (by positivity) (by linarith)
  · have h1 : 1 ≤ |z| := le_of_lt (lt_of_not_ge h)
    have he : |z|^(2*n)=z^(2*n) := by rw [pow_mul,pow_mul,sq_abs]
    calc
      (1+|z|)^n ≤ (2*|z|)^n := pow_le_pow_left₀ (by positivity) (by linarith) n
      _ = (2:ℝ)^n*|z|^n := mul_pow ..
      _ ≤ (2:ℝ)^n*|z|^(2*n) := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ h1 (by omega)) (by positivity)
      _ ≤ (2:ℝ)^n*(1+z^(2*n)) := by rw [he]; nlinarith [show (0:ℝ) ≤ 2^n by positivity]

lemma tilted_polynomial_bound {u f : ℝ → ℝ} {A B C κ Q a R δ : ℝ}
    (hu : Twice.RowTwiceTerminal u A B C κ Q) (ha : 0 ≤ a) (hR : 0 ≤ R)
    (hδ : 0 < δ) (hden : δ ≤ 1-a*κ*R^2)
    (hf : Measurable f) (hg : PolynomialGrowth f) :
    ∃ n : ℕ, ∃ H : ℝ, 0 ≤ H ∧ ∀ b : ℝ, 0 ≤ b → b ≤ R → ∀ x : ℝ,
      |∫ z : ℝ,f (x+b*z)*Real.exp (a*u (x+b*z)) ∂gaussianReal 0 1| ≤
        H*(1+|x|)^n*(∫ z : ℝ,Real.exp (a*u (x+b*z)) ∂gaussianReal 0 1) := by
  obtain ⟨n,D,hD,hfD⟩ := hg
  obtain ⟨H,hH,hbnd⟩ := tilted_even_moment_bound hu ha hR hδ hden n
  let K := D*(1+R)^n*(2:ℝ)^n
  have hK : 0 ≤ K := by dsimp [K]; positivity
  refine ⟨n+2*n,K*(1+H),by positivity,?_⟩
  intro b hb hbR x
  let w := fun z => Real.exp (a*u (x+b*z))
  let Z := ∫ z : ℝ,w z ∂gaussianReal 0 1
  let J := ∫ z : ℝ,z^(2*n)*w z ∂gaussianReal 0 1
  have hi : Integrable w (gaussianReal 0 1) := by
    simpa [w] using weighted_poly_integrable (x:=x) (b:=b) hu.differentiable.continuous
      (fun y => (hu.bounds y).2.1) ha (measurable_const (a:=1)) (PolynomialGrowth.const 1)
  have hiJ : Integrable (fun z : ℝ => z^(2*n)*w z) (gaussianReal 0 1) :=
    weighted_poly_integrable hu.differentiable.continuous (fun y => (hu.bounds y).2.1) ha
      (by fun_prop) (PolynomialGrowth.id.pow _)
  have hif : Integrable (fun z => f (x+b*z)*w z) (gaussianReal 0 1) :=
    weighted_poly_integrable hu.differentiable.continuous (fun y => (hu.bounds y).2.1) ha
      (hf.comp (by fun_prop)) ((show PolynomialGrowth f from ⟨n,D,hD,hfD⟩).affine x b)
  have hpoint (z : ℝ) : |f (x+b*z)*w z| ≤ K*(1+|x|)^n*(w z+z^(2*n)*w z) := by
    have hf0 : |f (x+b*z)| ≤ K*(1+|x|)^n*(1+z^(2*n)) := by
      have haa : 1+|x+b*z| ≤ ((1+R)*(1+|x|))*(1+|z|) := by
        have hh := heat_affine_bound x b z
        rw [abs_of_nonneg hb] at hh
        have hbr : 1+|x|+b ≤ (1+R)*(1+|x|) := by nlinarith [mul_nonneg hR (abs_nonneg x)]
        exact hh.trans (mul_le_mul_of_nonneg_right hbr (by positivity))
      calc
        |f (x+b*z)| ≤ D*(1+|x+b*z|)^n := hfD _
        _ ≤ D*(((1+R)*(1+|x|))*(1+|z|))^n := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) haa n) hD
        _ = (D*(1+R)^n*(1+|x|)^n)*(1+|z|)^n := by rw [mul_pow,mul_pow]; ring
        _ ≤ (D*(1+R)^n*(1+|x|)^n)*((2:ℝ)^n*(1+z^(2*n))) :=
          mul_le_mul_of_nonneg_left (one_abs_pow_le_even n z) (by positivity)
        _ = _ := by dsimp [K]; ring
    rw [abs_mul,abs_of_pos (Real.exp_pos _)]
    convert mul_le_mul_of_nonneg_right hf0 (Real.exp_pos (a*u (x+b*z))).le using 1
    first | rfl | (dsimp [w]; ring)
  have hh := integral_mono hif.abs ((hi.add hiJ).const_mul (K*(1+|x|)^n)) hpoint
  simp only [Pi.add_apply] at hh
  rw [integral_const_mul,integral_add hi hiJ] at hh
  have hZ : 0 ≤ Z := integral_nonneg (fun z => (Real.exp_pos _).le)
  have hbase : 1 ≤ (1+|x|)^(2*n) := one_le_pow₀ (by linarith [abs_nonneg x])
  have hJ : J ≤ H*(1+|x|)^(2*n)*Z := hbnd b hb hbR x
  have hsum : Z+J ≤ (1+H)*(1+|x|)^(2*n)*Z := by
    have hz := mul_le_mul_of_nonneg_right hbase hZ
    nlinarith only [hz,hJ]
  calc
    _ ≤ ∫ z : ℝ,|f (x+b*z)*w z| ∂gaussianReal 0 1 := abs_integral_le_integral_abs
    _ ≤ K*(1+|x|)^n*(Z+J) := hh
    _ ≤ K*(1+|x|)^n*((1+H)*(1+|x|)^(2*n)*Z) := mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = _ := by rw [pow_add]; dsimp [Z,w]; ring

end Higher
end MicroscopicJamming

 
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology

namespace MicroscopicJamming
namespace Higher

structure SmoothPolynomial (u : ℝ → ℝ) : Prop where
  smooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) u
  growth : ∀ n : ℕ, PolynomialGrowth (iteratedDeriv n u)

lemma SmoothPolynomial.differentiable {u : ℝ → ℝ} (hu : SmoothPolynomial u) (n : ℕ) :
    Differentiable ℝ (iteratedDeriv n u) :=
  hu.smooth.differentiable_iteratedDeriv n (by exact_mod_cast ENat.natCast_lt_top n)

lemma SmoothPolynomial.continuous {u : ℝ → ℝ} (hu : SmoothPolynomial u) (n : ℕ) :
    Continuous (iteratedDeriv n u) := (hu.differentiable n).continuous

lemma SmoothPolynomial.derivative {u : ℝ → ℝ} (hu : SmoothPolynomial u) :
    SmoothPolynomial (deriv u) := by
  refine ⟨(contDiff_infty_iff_deriv.mp hu.smooth).2,fun n => ?_⟩
  rw [← iteratedDeriv_succ']
  exact hu.growth (n+1)

lemma SmoothPolynomial.const_mul {u : ℝ → ℝ} (hu : SmoothPolynomial u) (a : ℝ) :
    SmoothPolynomial (fun x => a*u x) := by
  refine ⟨contDiff_const.mul hu.smooth,fun n => ?_⟩
  have he : iteratedDeriv n (fun x => a*u x) = fun x => a*iteratedDeriv n u x := by
    funext x
    exact iteratedDeriv_const_mul_field (n:=n) (x:=x) a u
  rw [he]
  exact (PolynomialGrowth.const a).mul (hu.growth n)

lemma SmoothPolynomial.exp {u : ℝ → ℝ} (hu : SmoothPolynomial u)
    {B : ℝ} (hb : ∀ x, u x ≤ B) : SmoothPolynomial (fun x => Real.exp (u x)) := by
  let v := fun x => Real.exp (u x)
  have hv : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) v := hu.smooth.exp
  have hdiff : deriv v = fun x => v x*deriv u x := by
    funext x
    simpa [v,mul_comm] using ((hu.smooth.differentiable (by simp) x).hasDerivAt.exp).deriv
  refine ⟨hv,?_⟩
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero =>
      simp only [iteratedDeriv_zero]
      exact PolynomialGrowth.of_bound (C:=Real.exp B) (fun x => by
        rw [abs_of_pos (Real.exp_pos _)]
        exact Real.exp_le_exp.mpr (hb x))
    | succ n =>
      rw [iteratedDeriv_succ',hdiff]
      have he : iteratedDeriv n (fun x => v x*deriv u x) =
          fun x => ∑ i ∈ Finset.range (n+1), (n.choose i:ℝ)*iteratedDeriv i v x*iteratedDeriv (n-i) (deriv u) x := by
        funext x
        exact iteratedDeriv_fun_mul (hv.of_le (by exact_mod_cast (le_top : (n : ℕ∞) ≤ ⊤))).contDiffAt
          (hu.derivative.smooth.of_le (by exact_mod_cast (le_top : (n : ℕ∞) ≤ ⊤))).contDiffAt
      rw [he]
      apply PolynomialGrowth.finset_sum
      intro i hi
      exact ((PolynomialGrowth.const (n.choose i:ℝ)).mul (ih i (Finset.mem_range.mp hi))).mul
        (hu.derivative.growth (n-i))

lemma row_terminal_smoothPolynomial {u : ℝ → ℝ} {A B C κ Q : ℝ}
    (hu : RowAnalyticTerminal u A B C κ Q) : SmoothPolynomial u := by
  refine ⟨hu.1,fun n => ?_⟩
  rcases n with _|_|n
  · simpa using PolynomialGrowth.of_quadratic (row_terminal_quadratic_growth hu)
  · simpa using PolynomialGrowth.of_quadratic (row_terminal_deriv_growth hu)
  · obtain ⟨K,hK⟩ := hu.2.2.2.2.2.1 (n+2) (by omega)
    exact PolynomialGrowth.of_bound hK

lemma heat_iterated_derivative {u : ℝ → ℝ} (hu : SmoothPolynomial u) (T : ℝ) (n : ℕ) :
    iteratedDeriv n (gaussianHeat u T) = gaussianHeat (iteratedDeriv n u) T := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [iteratedDeriv_succ,ih]
    funext x
    exact (space_derivative (hu.continuous n).measurable (hu.continuous (n+1)).measurable
      (hu.growth n) (hu.growth (n+1)) (fun y => by
        simpa only [iteratedDeriv_succ] using (hu.differentiable n y).hasDerivAt) T x).deriv

lemma heat_smooth {u : ℝ → ℝ} (hu : SmoothPolynomial u) (T : ℝ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (gaussianHeat u T) := by
  apply contDiff_of_differentiable_iteratedDeriv
  intro n _
  rw [heat_iterated_derivative hu]
  intro x
  exact (space_derivative (hu.continuous n).measurable (hu.continuous (n+1)).measurable
    (hu.growth n) (hu.growth (n+1)) (fun y => by
      simpa only [iteratedDeriv_succ] using (hu.differentiable n y).hasDerivAt) T x).differentiableAt

lemma heat_jet_time_derivative {u : ℝ → ℝ} (hu : SmoothPolynomial u) {T : ℝ}
    (hT : 0 < T) (n : ℕ) (x : ℝ) :
    HasDerivAt (fun r => gaussianHeat (iteratedDeriv n u) r x)
      ((1/2:ℝ)*gaussianHeat (iteratedDeriv (n+2) u) T x) T := by
  apply time_derivative (hu.continuous n).measurable (hu.continuous (n+1)).measurable
    (hu.continuous (n+2)).measurable (hu.growth n) (hu.growth (n+1)) (hu.growth (n+2))
    (fun y => by simpa only [iteratedDeriv_succ] using (hu.differentiable n y).hasDerivAt)
    (fun y => by simpa only [show n+2=(n+1)+1 by omega,iteratedDeriv_succ] using (hu.differentiable (n+1) y).hasDerivAt)
    hT x
end Higher
end MicroscopicJamming

 
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology

namespace MicroscopicJamming
namespace Higher

lemma SmoothPolynomial.const (c : ℝ) : SmoothPolynomial (fun _ : ℝ => c) := by
  refine ⟨contDiff_const,fun n => ?_⟩
  apply PolynomialGrowth.of_bound (C:=|c|)
  intro x
  rw [iteratedDeriv_const]
  split_ifs <;> simp

lemma SmoothPolynomial.add {u v : ℝ → ℝ} (hu : SmoothPolynomial u) (hv : SmoothPolynomial v) :
    SmoothPolynomial (fun x => u x+v x) := by
  refine ⟨hu.smooth.add hv.smooth,fun n => ?_⟩
  have he : iteratedDeriv n (fun x => u x+v x) = fun x => iteratedDeriv n u x+iteratedDeriv n v x := by
    funext x
    exact iteratedDeriv_fun_add
      (hu.smooth.of_le (by exact_mod_cast (le_top : (n : ℕ∞) ≤ ⊤))).contDiffAt
      (hv.smooth.of_le (by exact_mod_cast (le_top : (n : ℕ∞) ≤ ⊤))).contDiffAt
  rw [he]
  exact (hu.growth n).add (hv.growth n)

lemma SmoothPolynomial.mul {u v : ℝ → ℝ} (hu : SmoothPolynomial u) (hv : SmoothPolynomial v) :
    SmoothPolynomial (fun x => u x*v x) := by
  refine ⟨hu.smooth.mul hv.smooth,fun n => ?_⟩
  have he : iteratedDeriv n (fun x => u x*v x) =
      fun x => ∑ i ∈ Finset.range (n+1),(n.choose i:ℝ)*iteratedDeriv i u x*iteratedDeriv (n-i) v x := by
    funext x
    exact iteratedDeriv_fun_mul
      (hu.smooth.of_le (by exact_mod_cast (le_top : (n : ℕ∞) ≤ ⊤))).contDiffAt
      (hv.smooth.of_le (by exact_mod_cast (le_top : (n : ℕ∞) ≤ ⊤))).contDiffAt
  rw [he]
  exact PolynomialGrowth.finset_sum _ (fun i _ =>
    ((PolynomialGrowth.const (n.choose i:ℝ)).mul (hu.growth i)).mul (hv.growth (n-i)))

 

lemma exp_jet_factor {u : ℝ → ℝ} (hu : SmoothPolynomial u) (a : ℝ) (n : ℕ) :
    ∃ p : ℝ → ℝ, SmoothPolynomial p ∧
      iteratedDeriv n (fun x => Real.exp (a*u x)) = fun x => p x*Real.exp (a*u x) := by
  induction n with
  | zero => exact ⟨fun _ => 1,SmoothPolynomial.const 1,by simp⟩
  | succ n ih =>
    obtain ⟨p,hp,he⟩ := ih
    let q := fun x => deriv p x+(a*deriv u x)*p x
    refine ⟨q,hp.derivative.add ((hu.derivative.const_mul a).mul hp),?_⟩
    rw [iteratedDeriv_succ,he]
    funext x
    have hd := ((hp.smooth.differentiable (by simp) x).hasDerivAt).mul
      (((hu.smooth.differentiable (by simp) x).hasDerivAt.const_mul a).exp)
    convert hd.deriv using 1
    first | rfl | (dsimp [q]; ring)

end Higher
end MicroscopicJamming

end

end OAI
