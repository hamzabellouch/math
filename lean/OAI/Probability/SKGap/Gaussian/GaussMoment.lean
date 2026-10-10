import Mathlib
import OAI.Probability.SKGap.Model

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators NNReal
open MeasureTheory ProbabilityTheory
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal ENNReal
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal ENNReal
open MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix Matrix.Norms.Elementwise
open scoped BigOperators
open MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix Matrix.Norms.Elementwise
open scoped BigOperators
open scoped BigOperators NNReal ENNReal
open MeasureTheory Metric Set
open scoped BigOperators NNReal ENNReal
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators NNReal ENNReal Matrix.Norms.L2Operator
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Matrix.Norms.L2Operator
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Matrix Matrix.Norms.Elementwise
open MeasureTheory ProbabilityTheory Filter Set
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal ENNReal Matrix
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal ENNReal
open scoped BigOperators
open MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix Matrix.Norms.Elementwise NNReal ENNReal
open scoped BigOperators
open Filter Topology
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open Matrix
open scoped NNReal ENNReal BigOperators Topology Matrix.Norms.Elementwise
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal ENNReal Topology
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal ENNReal Topology
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology Matrix Matrix.Norms.Elementwise
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology Matrix Matrix.Norms.Elementwise
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology Matrix Matrix.Norms.Elementwise
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology Matrix Matrix.Norms.Elementwise
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology Matrix Matrix.Norms.Elementwise
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology Matrix Matrix.Norms.Elementwise
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology Matrix Matrix.Norms.Elementwise
open MeasureTheory ProbabilityTheory Filter Set Matrix
open scoped BigOperators NNReal ENNReal Matrix.Norms.L2Operator
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology Matrix Matrix.Norms.Elementwise
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology Matrix Matrix.Norms.Elementwise
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology Matrix Matrix.Norms.Elementwise
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology Matrix Matrix.Norms.Elementwise
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology Matrix Matrix.Norms.Elementwise
open Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
open Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
open MeasureTheory Filter
open scoped Topology NNReal ENNReal
namespace SKGapCutoff.Clock

noncomputable def gaussMoment (a : ℝ) (k : ℕ) (x : ℝ) : ℝ :=
  x^k*Real.exp (-a*x^2)

lemma integrable_gaussMoment {a : ℝ} (ha : 0 < a) (k : ℕ) :
    Integrable (gaussMoment a k) := by
  have hk : (-1:ℝ) < (k:ℝ) := by have := (Nat.cast_nonneg k : (0:ℝ)≤k); linarith
  have hh := integrable_rpow_mul_exp_neg_mul_sq ha hk
  convert! hh using 1
  ext x
  exact (Real.rpow_natCast x k).symm |> congrArg (fun t => t*Real.exp (-a*x^2))

lemma hasDerivAt_gaussMoment (a : ℝ) (k : ℕ) (x : ℝ) :
    HasDerivAt (gaussMoment a k)
      ((k:ℝ)*gaussMoment a (k-1) x-2*a*gaussMoment a (k+1) x) x := by
  have he := ((((hasDerivAt_id x).pow 2).const_mul (-a)).exp)
  convert! ((hasDerivAt_id x).pow k).mul he using 1
  simp only [gaussMoment,pow_succ,Pi.pow_apply,id_eq,Nat.cast_ofNat,mul_one,pow_zero]
  ring

lemma integrable_abs_add_one_pow_gauss {a : ℝ} (ha : 0 < a) (k : ℕ) :
    Integrable (fun x : ℝ => (|x|+1)^k*Real.exp (-a*x^2)) := by
  have hi (j : ℕ) : Integrable (fun x : ℝ => |x|^j*Real.exp (-a*x^2)) := by
    simpa only [gaussMoment,Real.norm_eq_abs,abs_mul,abs_pow,
      abs_of_nonneg (Real.exp_nonneg _)] using (integrable_gaussMoment ha j).norm
  have hh := integrable_finsetSum (Finset.range (k+1))
    (fun j _ => (hi j).mul_const (k.choose j:ℝ))
  convert! hh using 1
  ext x
  rw [add_pow,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [one_pow,mul_one]
  ring

noncomputable def momentEnvelope (a : ℝ) (k : ℕ) (x : ℝ) : ℝ :=
  ((k:ℝ)*(|x|+1)^(k-1)+2*a*(|x|+1)^(k+1))*Real.exp a*Real.exp (-(a/2)*x^2)

lemma integrable_momentEnvelope {a : ℝ} (ha : 0 < a) (k : ℕ) :
    Integrable (momentEnvelope a k) := by
  have hhalf : 0 < a/2 := by positivity
  have hh := (((integrable_abs_add_one_pow_gauss hhalf (k-1)).const_mul (k:ℝ)).add
    ((integrable_abs_add_one_pow_gauss hhalf (k+1)).const_mul (2*a))).const_mul (Real.exp a)
  convert! hh using 1
  ext x
  simp only [momentEnvelope,Pi.add_apply]
  ring

lemma gaussMoment_deriv_bound {a : ℝ} (ha : 0 < a) (k : ℕ) (x z : ℝ)
    (hz : z ∈ Set.Icc (x-1) (x+1)) :
    |(k:ℝ)*gaussMoment a (k-1) z-2*a*gaussMoment a (k+1) z| ≤
      momentEnvelope a k x := by
  have hdist : |z-x| ≤ 1 := abs_le.mpr ⟨by linarith [hz.1],by linarith [hz.2]⟩
  have hzabs : |z| ≤ |x|+1 := by
    calc
      |z| = |(z-x)+x| := by rw [sub_add_cancel]
      _ ≤ |z-x|+|x| := abs_add_le _ _
      _ ≤ |x|+1 := by linarith
  have hsq : (z-x)^2 ≤ 1 := by
    have hh := mul_self_le_mul_self (abs_nonneg (z-x)) hdist
    nlinarith [sq_abs (z-x)]
  have hquad : x^2/2-1 ≤ z^2 := by nlinarith [sq_nonneg (x-2*z)]
  have he : Real.exp (-a*z^2) ≤ Real.exp a*Real.exp (-(a/2)*x^2) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith [mul_nonneg ha.le (sub_nonneg.mpr hquad)]
  have h1 := pow_le_pow_left₀ (abs_nonneg z) hzabs (k-1)
  have h2 := pow_le_pow_left₀ (abs_nonneg z) hzabs (k+1)
  calc
    _ ≤ |(k:ℝ)*gaussMoment a (k-1) z|+|2*a*gaussMoment a (k+1) z| := by
      simpa only [Real.norm_eq_abs] using norm_sub_le
        ((k:ℝ)*gaussMoment a (k-1) z) (2*a*gaussMoment a (k+1) z)
    _ = ((k:ℝ)*|z|^(k-1)+2*a*|z|^(k+1))*Real.exp (-a*z^2) := by
      norm_num only [gaussMoment,abs_mul,abs_pow,abs_of_nonneg (Nat.cast_nonneg k : (0:ℝ)≤k),
        abs_of_nonneg ha.le,abs_of_nonneg (Real.exp_nonneg _)]
      ring
    _ ≤ ((k:ℝ)*(|x|+1)^(k-1)+2*a*(|x|+1)^(k+1))*
        (Real.exp a*Real.exp (-(a/2)*x^2)) := by
      apply mul_le_mul _ he (Real.exp_nonneg _) (by positivity)
      exact add_le_add (mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg _))
        (mul_le_mul_of_nonneg_left h2 (by positivity))
    _ = _ := by dsimp [momentEnvelope]; ring

noncomputable def diffMoment (a : ℝ) (k : ℕ) (h x : ℝ) : ℝ :=
  (gaussMoment a k (x+h)-gaussMoment a k x)/h

lemma diffMoment_bound {a : ℝ} (ha : 0 < a) (k : ℕ) {h : ℝ}
    (hh : 0 < h) (hh1 : h ≤ 1) (x : ℝ) :
    |diffMoment a k h x| ≤ momentEnvelope a k x := by
  have hmv := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (s := Set.Icc (x-1) (x+1))
    (f := gaussMoment a k)
    (f' := fun z => (k:ℝ)*gaussMoment a (k-1) z-2*a*gaussMoment a (k+1) z)
    (fun z _ => (hasDerivAt_gaussMoment a k z).hasDerivWithinAt)
    (fun z hz => by simpa only [Real.norm_eq_abs] using gaussMoment_deriv_bound ha k x z hz)
    (convex_Icc _ _) (show x ∈ Set.Icc (x-1) (x+1) from ⟨by linarith,by linarith⟩)
    (show x+h ∈ Set.Icc (x-1) (x+1) from ⟨by linarith,by linarith⟩)
  rw [Real.norm_eq_abs,Real.norm_eq_abs,add_sub_cancel_left,abs_of_pos hh] at hmv
  unfold diffMoment
  rw [abs_div,abs_of_pos hh]
  exact (div_le_iff₀ hh).mpr hmv

lemma integrable_diffMoment {a : ℝ} (ha : 0 < a) (k : ℕ) (h : ℝ) :
    Integrable (diffMoment a k h) :=
  (((integrable_gaussMoment ha k).comp_add_right h).sub
    (integrable_gaussMoment ha k)).div_const h

lemma gaussMoment_derivative_L1 {a : ℝ} (ha : 0 < a) (k : ℕ) :
    Tendsto (fun n : ℕ => ∫ x : ℝ,
      |diffMoment a k (1/((n:ℝ)+1)) x-
        ((k:ℝ)*gaussMoment a (k-1) x-2*a*gaussMoment a (k+1) x)|)
      atTop (𝓝 0) := by
  let dg : ℝ → ℝ := fun x => (k:ℝ)*gaussMoment a (k-1) x-2*a*gaussMoment a (k+1) x
  have hdg : Integrable dg := ((integrable_gaussMoment ha (k-1)).const_mul (k:ℝ)).sub
    ((integrable_gaussMoment ha (k+1)).const_mul (2*a))
  have hstep : Tendsto (fun n : ℕ => 1/((n:ℝ)+1)) atTop (𝓝[≠] (0:ℝ)) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨tendsto_one_div_add_atTop_nhds_zero_nat, ?_⟩
    exact Filter.Eventually.of_forall (fun n => by
      simp only [Set.mem_compl_iff,Set.mem_singleton_iff]
      exact ne_of_gt (by positivity))
  have hp (x : ℝ) : Tendsto (fun n : ℕ => diffMoment a k (1/((n:ℝ)+1)) x)
      atTop (𝓝 (dg x)) := by
    have hh := (hasDerivAt_gaussMoment a k x).tendsto_slope_zero.comp hstep
    simpa only [Function.comp_def,smul_eq_mul,div_eq_mul_inv,mul_comm,diffMoment,dg] using hh
  have ht := tendsto_integral_of_dominated_convergence
    (fun x => momentEnvelope a k x+|dg x|)
    (F := fun n : ℕ => fun x => |diffMoment a k (1/((n:ℝ)+1)) x-dg x|)
    (f := fun _ => (0:ℝ))
    (fun n => ((integrable_diffMoment ha k _).sub hdg).abs.aestronglyMeasurable)
    ((integrable_momentEnvelope ha k).add hdg.abs)
    (fun n => Filter.Eventually.of_forall (fun x => by
      rw [Real.norm_eq_abs,abs_abs]
      have htri : |diffMoment a k (1/((n:ℝ)+1)) x-dg x| ≤
          |diffMoment a k (1/((n:ℝ)+1)) x|+|dg x| := by
        simpa only [Real.norm_eq_abs] using
          norm_sub_le (diffMoment a k (1/((n:ℝ)+1)) x) (dg x)
      exact htri.trans (add_le_add (diffMoment_bound ha k (h := 1/((n:ℝ)+1)) (by positivity)
            (by have := (Nat.cast_nonneg n : (0:ℝ)≤n); apply (div_le_one (by positivity)).mpr; linarith) x) le_rfl)))
    (Filter.Eventually.of_forall (fun x => by simpa using ((hp x).sub_const (dg x)).abs))
  simpa only [integral_zero] using ht

noncomputable def momentL1 (a : ℝ) (ha : 0 < a) (k : ℕ) (y : ℝ) : Lp ℝ 1 (volume : Measure ℝ) :=
  Integrable.toL1 (fun x : ℝ => gaussMoment a k (x+y))
    ((integrable_gaussMoment ha k).comp_add_right y)

lemma norm_toL1_real {f : ℝ → ℝ} (hf : Integrable f) :
    ‖hf.toL1 f‖ = ∫ x : ℝ, |f x| := by
  rw [Integrable.norm_toL1_eq_lintegral_enorm,
    ← integral_norm_eq_lintegral_enorm hf.aestronglyMeasurable]
  simp only [Real.norm_eq_abs]

lemma momentL1_derivative {a : ℝ} (ha : 0 < a) (k : ℕ) (y : ℝ) :
    Tendsto (fun n : ℕ => ((1/((n:ℝ)+1))⁻¹) •
      (momentL1 a ha k (y+1/((n:ℝ)+1))-momentL1 a ha k y)) atTop
      (𝓝 ((k:ℝ) • momentL1 a ha (k-1) y-(2*a) • momentL1 a ha (k+1) y)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have he (n : ℕ) :
      ‖((1/((n:ℝ)+1))⁻¹) • (momentL1 a ha k (y+1/((n:ℝ)+1))-
        momentL1 a ha k y)-((k:ℝ) • momentL1 a ha (k-1) y-
          (2*a) • momentL1 a ha (k+1) y)‖ =
      ∫ x : ℝ, |diffMoment a k (1/((n:ℝ)+1)) x-
        ((k:ℝ)*gaussMoment a (k-1) x-2*a*gaussMoment a (k+1) x)| := by
    let h : ℝ := 1/((n:ℝ)+1)
    let f : ℝ → ℝ := fun x => h⁻¹ * (gaussMoment a k (x+(y+h))-
      gaussMoment a k (x+y))-
      ((k:ℝ)*gaussMoment a (k-1) (x+y)-(2*a)*gaussMoment a (k+1) (x+y))
    have hf : Integrable f :=
      ((((integrable_gaussMoment ha k).comp_add_right (y+h)).sub
        ((integrable_gaussMoment ha k).comp_add_right y)).const_mul h⁻¹).sub
      ((((integrable_gaussMoment ha (k-1)).comp_add_right y).const_mul (k:ℝ)).sub
        (((integrable_gaussMoment ha (k+1)).comp_add_right y).const_mul (2*a)))
    change ‖hf.toL1 f‖ = _
    rw [norm_toL1_real]
    have hfun : (fun x => |f x|) = fun x => |diffMoment a k h (x+y)-
        ((k:ℝ)*gaussMoment a (k-1) (x+y)-2*a*gaussMoment a (k+1) (x+y))| := by
      funext x
      simp only [f,diffMoment,add_assoc,div_eq_mul_inv,mul_comm]
    rw [hfun]
    exact integral_add_right_eq_self (fun x => |diffMoment a k h x-
      ((k:ℝ)*gaussMoment a (k-1) x-2*a*gaussMoment a (k+1) x)|) y
  simp_rw [he]
  exact gaussMoment_derivative_L1 ha k

lemma momentL1_mem_of_gaussian {a : ℝ} (ha : 0 < a)
    (S : Submodule ℝ (Lp ℝ 1 (volume : Measure ℝ))) (hS : IsClosed (S : Set (Lp ℝ 1 (volume : Measure ℝ))))
    (hbase : ∀ y, momentL1 a ha 0 y ∈ S) :
    ∀ k y, momentL1 a ha k y ∈ S := by
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro y
    cases k with
    | zero => exact hbase y
    | succ k =>
      have hder : (k:ℝ) • momentL1 a ha (k-1) y-
          (2*a) • momentL1 a ha (k+1) y ∈ S :=
        hS.mem_of_tendsto (momentL1_derivative ha k y)
          (Filter.Eventually.of_forall (fun n => S.smul_mem _
            (S.sub_mem (ih k (by omega) _) (ih k (by omega) _))))
      have hlow : (k:ℝ) • momentL1 a ha (k-1) y ∈ S :=
        S.smul_mem _ (ih (k-1) (by omega) y)
      have hhigh := S.sub_mem hlow hder
      rw [sub_sub_cancel] at hhigh
      have hn : (2*a) ≠ 0 := ne_of_gt (by positivity)
      have hh := S.smul_mem (2*a)⁻¹ hhigh
      simpa only [smul_smul,inv_mul_cancel₀ hn,one_smul] using hh

noncomputable def gaussianTaylor (a c : ℝ) (N : ℕ) (x : ℝ) : ℝ :=
  ∑ k ∈ Finset.range N, ((-c)^k/(Nat.factorial k : ℝ))*gaussMoment a (2*k) x

lemma gaussianTaylor_eq (a c : ℝ) (N : ℕ) (x : ℝ) :
    gaussianTaylor a c N x =
    (∑ k ∈ Finset.range N, (-c*x^2)^k/(Nat.factorial k : ℝ))*Real.exp (-a*x^2) := by
  unfold gaussianTaylor gaussMoment
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k _
  rw [mul_pow,← pow_mul]
  ring

lemma gaussianTaylor_bound (a : ℝ) {c : ℝ} (hc : 0 ≤ c) (N : ℕ) (x : ℝ) :
    |gaussianTaylor a c N x| ≤ Real.exp (-(a-c)*x^2) := by
  rw [gaussianTaylor_eq,abs_mul,abs_of_pos (Real.exp_pos _)]
  have habs : |∑ k ∈ Finset.range N, (-c*x^2)^k/(Nat.factorial k : ℝ)| ≤
      ∑ k ∈ Finset.range N, (c*x^2)^k/(Nat.factorial k : ℝ) := by
    calc
      _ ≤ ∑ k ∈ Finset.range N, |(-c*x^2)^k/(Nat.factorial k : ℝ)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ = _ := by
        apply Finset.sum_congr rfl
        intro k _
        rw [abs_div,abs_pow,abs_mul,abs_neg,abs_of_nonneg hc,
          abs_of_nonneg (sq_nonneg x),abs_of_nonneg (Nat.cast_nonneg _)]
  calc
    _ ≤ Real.exp (c*x^2)*Real.exp (-a*x^2) :=
      mul_le_mul_of_nonneg_right (habs.trans (Real.sum_le_exp_of_nonneg (by positivity) N))
        (Real.exp_nonneg _)
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

lemma integrable_gaussianTaylor {a : ℝ} (ha : 0 < a) (c : ℝ) (N : ℕ) :
    Integrable (gaussianTaylor a c N) :=
  integrable_finsetSum _ (fun k _ => (integrable_gaussMoment ha (2*k)).const_mul _)

lemma gaussianTaylor_tendsto (a c x : ℝ) :
    Tendsto (fun N : ℕ => gaussianTaylor a c N x) atTop (𝓝 (gaussMoment (a+c) 0 x)) := by
  have ht := (NormedSpace.expSeries_div_hasSum_exp (-c*x^2)).tendsto_sum_nat.mul_const
    (Real.exp (-a*x^2))
  simpa only [gaussianTaylor_eq,← Real.exp_eq_exp_ℝ,← Real.exp_add,gaussMoment,pow_zero,one_mul,
    show -c*x^2+-a*x^2=-(a+c)*x^2 by ring] using ht

lemma gaussianTaylor_L1 {a c : ℝ} (ha : 0 < a) (hc : 0 ≤ c) (hca : c < a) :
    Tendsto (fun N : ℕ => ∫ x : ℝ,
      |gaussianTaylor a c N x-gaussMoment (a+c) 0 x|) atTop (𝓝 0) := by
  have hp : 0 < a+c := by linarith
  have hm : 0 < a-c := by linarith
  have hh := tendsto_integral_of_dominated_convergence
    (fun x => Real.exp (-(a-c)*x^2)+Real.exp (-(a+c)*x^2))
    (F := fun N : ℕ => fun x => |gaussianTaylor a c N x-gaussMoment (a+c) 0 x|)
    (f := fun _ => (0:ℝ))
    (fun N => ((integrable_gaussianTaylor ha c N).sub (integrable_gaussMoment hp 0)).abs.aestronglyMeasurable)
    (by simpa only [Pi.add_def,gaussMoment,pow_zero,one_mul] using
      (integrable_gaussMoment hm 0).add (integrable_gaussMoment hp 0))
    (fun N => Filter.Eventually.of_forall (fun x => by
      rw [Real.norm_eq_abs,abs_abs]
      have htri := norm_sub_le (gaussianTaylor a c N x) (gaussMoment (a+c) 0 x)
      simp only [Real.norm_eq_abs,gaussMoment,pow_zero,one_mul,abs_of_pos (Real.exp_pos _)] at htri
      simpa only [gaussMoment,pow_zero,one_mul] using
        htri.trans (add_le_add (gaussianTaylor_bound a hc N x) le_rfl)))
    (Filter.Eventually.of_forall (fun x => by
      simpa using ((gaussianTaylor_tendsto a c x).sub_const (gaussMoment (a+c) 0 x)).abs))
  simpa only [integral_zero] using hh

lemma toL1_finsetSum {ι : Type*} (s : Finset ι) (f : ι → ℝ → ℝ)
    (hf : ∀ i, Integrable (f i)) :
    (integrable_finsetSum s (fun i _ => hf i)).toL1 (fun x => ∑ i ∈ s, f i x) =
      ∑ i ∈ s, (hf i).toL1 (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact Integrable.toL1_zero _
  | @insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    change (((hf i).add (integrable_finsetSum s (fun j _ => hf j))).toL1
      (f i+(fun x => ∑ j ∈ s, f j x))) = _
    rw [Integrable.toL1_add _ _ (hf i)
      (integrable_finsetSum s (fun j _ => hf j)),ih]

lemma toL1_tendsto_of_integral_abs_sub {f : ℕ → ℝ → ℝ} {g : ℝ → ℝ}
    (hf : ∀ n, Integrable (f n)) (hg : Integrable g)
    (ht : Tendsto (fun n => ∫ x : ℝ, |f n x-g x|) atTop (𝓝 0)) :
    Tendsto (fun n => (hf n).toL1 (f n)) atTop (𝓝 (hg.toL1 g)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have he (n : ℕ) : ‖(hf n).toL1 (f n)-hg.toL1 g‖ = ∫ x : ℝ, |f n x-g x| := by
    change ‖((hf n).sub hg).toL1 (f n-g)‖ = _
    exact norm_toL1_real _
  simpa only [he] using ht

lemma gaussian_increment_mem {a c : ℝ} (ha : 0 < a) (hc : 0 ≤ c) (hca : c < a)
    (S : Submodule ℝ (Lp ℝ 1 (volume : Measure ℝ)))
    (hS : IsClosed (S : Set (Lp ℝ 1 (volume : Measure ℝ))))
    (hbase : ∀ y, momentL1 a ha 0 y ∈ S) :
    ∀ y, momentL1 (a+c) (by linarith) 0 y ∈ S := by
  intro y
  have hm := momentL1_mem_of_gaussian ha S hS hbase
  let fp : ℕ → ℝ → ℝ := fun N x => gaussianTaylor a c N (x+y)
  have hfp (N : ℕ) : Integrable (fp N) := (integrable_gaussianTaylor ha c N).comp_add_right y
  have hin (N : ℕ) : (hfp N).toL1 (fp N) ∈ S := by
    have he : (hfp N).toL1 (fp N) =
        ∑ k ∈ Finset.range N, ((-c)^k/(Nat.factorial k:ℝ)) • momentL1 a ha (2*k) y := by
      exact toL1_finsetSum (Finset.range N)
        (fun k x => ((-c)^k/(Nat.factorial k:ℝ))*gaussMoment a (2*k) (x+y))
        (fun k => ((integrable_gaussMoment ha (2*k)).comp_add_right y).const_mul _)
    rw [he]
    exact S.sum_mem (fun k _ => S.smul_mem _ (hm _ y))
  have ht : Tendsto (fun N => ∫ x : ℝ,
      |fp N x-gaussMoment (a+c) 0 (x+y)|) atTop (𝓝 0) := by
    have he (N : ℕ) : (∫ x : ℝ, |fp N x-gaussMoment (a+c) 0 (x+y)|) =
        ∫ x : ℝ, |gaussianTaylor a c N x-gaussMoment (a+c) 0 x| :=
      integral_add_right_eq_self (fun x => |gaussianTaylor a c N x-gaussMoment (a+c) 0 x|) y
    simpa only [he] using gaussianTaylor_L1 ha hc hca
  exact hS.mem_of_tendsto (toL1_tendsto_of_integral_abs_sub hfp
    ((integrable_gaussMoment (by linarith : 0 < a+c) 0).comp_add_right y) ht)
    (Filter.Eventually.of_forall hin)

lemma gaussian_wider_precision_mem {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (S : Submodule ℝ (Lp ℝ 1 (volume : Measure ℝ)))
    (hS : IsClosed (S : Set (Lp ℝ 1 (volume : Measure ℝ))))
    (hbase : ∀ y, momentL1 a ha 0 y ∈ S) :
    ∀ y, momentL1 b (ha.trans_le hab) 0 y ∈ S := by
  obtain ⟨N,hN⟩ := exists_nat_gt ((b-a)/a+1)
  have hN0 : (0:ℝ) < N := by
    have : 0 ≤ (b-a)/a := div_nonneg (sub_nonneg.mpr hab) ha.le
    linarith
  let c : ℝ := (b-a)/N
  have hc : 0 ≤ c := div_nonneg (sub_nonneg.mpr hab) hN0.le
  have hca : c < a := by
    apply (div_lt_iff₀ hN0).mpr
    have : (b-a)/a < (N:ℝ) := by linarith
    have := (div_lt_iff₀ ha).mp this
    linarith
  have hall (n : ℕ) : ∀ y, momentL1 (a+(n:ℝ)*c) (by positivity) 0 y ∈ S := by
    induction n with
    | zero => simpa only [Nat.cast_zero,zero_mul,add_zero] using hbase
    | succ n ih =>
      have hh := gaussian_increment_mem (show 0 < a+(n:ℝ)*c by positivity) hc
        (show c < a+(n:ℝ)*c by have := mul_nonneg (Nat.cast_nonneg n) hc; linarith) S hS ih
      have he : a+(↑(n+1):ℝ)*c=(a+(n:ℝ)*c)+c := by push_cast; ring
      simpa only [he] using hh
  have he : a+(N:ℝ)*c = b := by dsimp [c]; field_simp [ne_of_gt hN0]; ring
  simpa only [he] using hall N

lemma gaussian_mem_closed_span {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (y : ℝ) :
    momentL1 b (ha.trans_le hab) 0 y ∈
      (Submodule.span ℝ (Set.range (momentL1 a ha 0))).topologicalClosure := by
  apply gaussian_wider_precision_mem ha hab _
    (Submodule.isClosed_topologicalClosure _) (fun z => ?_) y
  exact Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨z,rfl⟩)

theorem finite_gaussian_approximation {a b ε : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hε : 0 < ε) :
    ∃ (s : Finset ℝ) (c : ℝ → ℝ),
      (∫ x : ℝ, |gaussMoment b 0 x-
        ∑ y ∈ s, c y*gaussMoment a 0 (x+y)|) < ε := by
  classical
  have hm := gaussian_mem_closed_span ha hab 0
  change momentL1 b (ha.trans_le hab) 0 0 ∈
    closure (↑(Submodule.span ℝ (Set.range (momentL1 a ha 0))) : Set _) at hm
  obtain ⟨w,hw,hclose⟩ := Metric.mem_closure_iff.mp hm ε hε
  obtain ⟨c,rfl⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp hw
  refine ⟨c.support,c,?_⟩
  let f : ℝ → ℝ := fun x => ∑ y ∈ c.support, c y*gaussMoment a 0 (x+y)
  have hf : Integrable f := integrable_finsetSum _ (fun y _ =>
    ((integrable_gaussMoment ha 0).comp_add_right y).const_mul (c y))
  have hfL : hf.toL1 f = c.sum (fun y z => z • momentL1 a ha 0 y) :=
    toL1_finsetSum c.support (fun y x => c y*gaussMoment a 0 (x+y))
      (fun y => ((integrable_gaussMoment ha 0).comp_add_right y).const_mul (c y))
  rw [dist_eq_norm,← hfL] at hclose
  change ‖((((integrable_gaussMoment (ha.trans_le hab) 0).comp_add_right 0).sub hf).toL1
    (fun x => gaussMoment b 0 (x+0)-f x))‖ < ε at hclose
  rw [norm_toL1_real] at hclose
  simpa only [add_zero] using hclose

end SKGapCutoff.Clock

open MeasureTheory Filter ProbabilityTheory
open scoped Topology NNReal ENNReal

end

end OAI
