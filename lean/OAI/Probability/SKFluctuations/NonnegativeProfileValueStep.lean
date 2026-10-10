import Mathlib
import OAI.Probability.SKFluctuations.UniformGridConvergence

namespace OAI

/-! Nonnegative Profile Value Step. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology
open MeasureTheory Filter Set
open scoped Topology
open MeasureTheory ProbabilityTheory Filter Set
namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal BigOperators

 

 theorem HeatJet.nonnegativeProfileValue_step {n : ℕ} (J : HeatJet n)
    (α : NonnegativeMassProfile) {b : ℝ} (hb : 0 < b) (l : ℝ) (t : ℝ≥0)
    (ht : 0 < (t:ℝ)) (j : ℕ)
    (hc : ∀ s ∈ Ico l (l+t), α.mass s = if s < l+(t:ℝ)/2^j then 0 else b)
    (x : Fin (n+1) → ℝ) :
    J.nonnegativeProfileValue α l t x = zeroContinuation
      (Measure.pi fun _ : Fin (n+1) => gaussianReal 0 (Real.toNNReal ((t:ℝ)/2^j)))
      (clockContinuation b J.F ((t:ℝ)-(t:ℝ)/2^j)) x := by
  let e : ℕ → ℝ := fun k => (1/2:ℝ)^k
  have he (k : ℕ) : 0 < e k := by dsimp [e]; positivity
  have hq : 0 ≤ (t:ℝ)-(t:ℝ)/2^j := by
    apply sub_nonneg.mpr
    exact div_le_self ht.le (one_le_pow₀ (by norm_num : (1:ℝ) ≤ 2))
  have hp : Tendsto e atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hp' : Tendsto e atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨hp,Filter.Eventually.of_forall he⟩
  let F := clockContinuation b J.F ((t:ℝ)-(t:ℝ)/2^j)
  have hF : LipschitzWith J.C F := (J.evolve hb _).lipschitz
  have hl := (shiftedContinuation_tendsto_zero_mass hF
    (exponentialIncrement_gaussian (fun _ : Fin (n+1) => Real.toNNReal ((t:ℝ)/2^j))) x).comp hp'
  change Tendsto (fun k => clockContinuation (e k) F ((t:ℝ)/2^j) x) atTop _ at hl
  have hs (k : ℕ) : J.profileValue (α.positiveApprox k) l t x =
      clockContinuation (e k) (clockContinuation (b+e k) J.F ((t:ℝ)-(t:ℝ)/2^j)) ((t:ℝ)/2^j) x := by
    apply J.profileValue_step (α.positiveApprox k) (he k) (add_pos hb (he k)) l t ht j
    intro s hs
    dsimp only [NonnegativeMassProfile.positiveApprox]
    rw [hc s hs]
    split_ifs <;> simp only [zero_add,e]
  choose D _ hD using fun i => (J.smoothG i).bound
  have hd (k : ℕ) : dist (clockContinuation (e k) F ((t:ℝ)/2^j) x)
      (J.profileValue (α.positiveApprox k) l t x) ≤
      e k/2*(∑ i, (D i)^2)*((t:ℝ)-(t:ℝ)/2^j) := by
    rw [hs,Real.dist_eq,abs_sub_comm]
    apply clockContinuation_abs_sub_le (J.evolve (add_pos hb (he k)) _).lipschitz
      hF (he k)
    intro y
    have h := J.potential_mass_difference D hD (add_pos hb (he k)) hb hq y
    simpa only [HeatJet.evolve,F,add_sub_cancel_left,abs_of_pos (he k)] using h
  have htend : Tendsto (fun k => dist (clockContinuation (e k) F ((t:ℝ)/2^j) x)
      (J.profileValue (α.positiveApprox k) l t x)) atTop (𝓝 0) := by
    apply squeeze_zero (fun _ => dist_nonneg) hd
    simpa only [zero_div,zero_mul] using
      ((hp.div_const 2).mul_const (∑ i, (D i)^2)).mul_const ((t:ℝ)-(t:ℝ)/2^j)
  exact tendsto_nhds_unique (J.regularized_tendsto α l t x) (hl.congr_dist htend)

end SKFluctuations.Hierarchy

namespace SKFluctuations.Scalar
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal

 theorem gaussian_cosh_integrable (x : ℝ) (t : ℝ≥0) :
    Integrable (fun y => Real.cosh (x+y)) (gaussianReal 0 t) := by
  have hp := (integrable_exp_mul_gaussianReal (μ := 0) (v := t) 1).const_mul (Real.exp x)
  have hm := (integrable_exp_mul_gaussianReal (μ := 0) (v := t) (-1)).const_mul (Real.exp (-x))
  convert (hp.add hm).div_const 2 using 1
  funext y
  rw [Real.cosh_eq]
  simp only [Pi.add_apply,one_mul,neg_one_mul,neg_add_rev,Real.exp_add]
  ring

 theorem gaussian_cosh (x : ℝ) (t : ℝ≥0) :
    (∫ y, Real.cosh (x+y) ∂gaussianReal 0 t) = Real.exp ((t:ℝ)/2)*Real.cosh x := by
  have hp := (integrable_exp_mul_gaussianReal (μ := 0) (v := t) 1).const_mul (Real.exp x)
  have hm := (integrable_exp_mul_gaussianReal (μ := 0) (v := t) (-1)).const_mul (Real.exp (-x))
  have he : (fun y => Real.cosh (x+y)) = (fun y =>
      (Real.exp x*Real.exp (1*y)+Real.exp (-x)*Real.exp (-1*y))/2) := by
    funext y
    rw [Real.cosh_eq]
    simp only [one_mul,neg_one_mul,neg_add_rev,Real.exp_add]
    ring
  rw [he,integral_div,integral_add hp hm,integral_const_mul,integral_const_mul]
  have hi (a : ℝ) : (∫ y, Real.exp (a*y) ∂gaussianReal 0 t) = Real.exp ((t:ℝ)*a^2/2) := by
    simpa only [mgf,zero_mul,zero_add] using congrFun (mgf_fun_id_gaussianReal (μ := 0) (v := t)) a
  rw [hi 1,hi (-1)]
  norm_num only [one_pow,neg_one_sq,mul_one]
  rw [Real.cosh_eq]
  ring

end SKFluctuations.Scalar

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal BigOperators

 theorem integral_gaussian_eval {ι : Type*} [Fintype ι] (i : ι) (t : ℝ≥0)
    {f : ℝ → ℝ} (hf : Continuous f) :
    (∫ z : ι → ℝ, f (z i) ∂Measure.pi fun _ : ι => gaussianReal 0 t) =
      ∫ y, f y ∂gaussianReal 0 t := by
  have hh := integral_map_of_stronglyMeasurable (μ := Measure.pi fun _ : ι => gaussianReal 0 t)
    (measurable_pi_apply i) hf.stronglyMeasurable
  rw [(measurePreserving_eval (fun _ : ι => gaussianReal 0 t) i).map_eq] at hh
  exact hh.symm

 

theorem scalarTerminal_mass_one (t : ℝ≥0) (x : Fin 1 → ℝ) :
    clockContinuation 1 scalarTerminal.F t x = Real.log (Real.cosh (x 0))+(t:ℝ)/2 := by
  change Real.log (∫ z, Real.exp (1*scalarTerminal.F (x+z))
    ∂Measure.pi fun _ : Fin 1 => gaussianReal 0 (Real.toNNReal (t:ℝ)))/1 = _
  rw [Real.toNNReal_coe]
  simp only [one_mul,div_one,scalarTerminal_F,Pi.add_apply,Real.exp_log (Real.cosh_pos _)]
  rw [integral_gaussian_eval (ι := Fin 1) (0 : Fin 1) t (f := fun y => Real.cosh (x 0+y)) (by fun_prop),Scalar.gaussian_cosh]
  rw [Real.log_mul (Real.exp_ne_zero _) (ne_of_gt (Real.cosh_pos _)),Real.log_exp]
  ring

end SKFluctuations.Hierarchy

namespace SKFluctuations.GaussianCalculus
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal

 

def ExpBounded (f : ℝ → ℝ) : Prop :=
  Continuous f ∧ ∃ C c : ℝ, 0 ≤ C ∧ 0 ≤ c ∧ ∀ x, |f x| ≤ C * Real.exp (c*|x|)

theorem standardGaussian_exp_abs_integrable (c : ℝ) :
    Integrable (fun x : ℝ => Real.exp (c*|x|)) (gaussianReal 0 1) := by
  apply ((integrable_exp_mul_gaussianReal (μ := 0) (v := 1) c).add
    (integrable_exp_mul_gaussianReal (μ := 0) (v := 1) (-c))).mono'
  · exact (Real.continuous_exp.comp (continuous_abs.const_mul c)).aestronglyMeasurable
  · filter_upwards [] with z
    change |Real.exp (c*|z|)| ≤ Real.exp (c*z) + Real.exp (-c*z)
    rw [abs_of_pos (Real.exp_pos _)]
    rcases le_total 0 z with hz | hz
    · rw [abs_of_nonneg hz]
      exact le_add_of_nonneg_right (Real.exp_nonneg _)
    · rw [abs_of_nonpos hz, mul_neg, neg_mul]
      exact le_add_of_nonneg_left (Real.exp_nonneg _)

 theorem affine_exp_bound {f : ℝ → ℝ} {C c : ℝ}
    (hC : 0 ≤ C) (hc : 0 ≤ c) (hb : ∀ x, |f x| ≤ C*Real.exp (c*|x|))
    (x a z : ℝ) : |f (x+a*z)| ≤ C*Real.exp (c*|x|)*Real.exp (c*|a| *|z|) := by
  calc
    _ ≤ C*Real.exp (c*|x+a*z|) := hb _
    _ ≤ C*Real.exp (c*(|x|+|a| *|z|)) := by
      gcongr
      simpa only [abs_mul] using abs_add_le x (a*z)
    _ = _ := by rw [mul_add, Real.exp_add]; ring_nf

 theorem affine_z_exp_bound {f : ℝ → ℝ} {C c : ℝ}
    (hC : 0 ≤ C) (hc : 0 ≤ c) (hb : ∀ x, |f x| ≤ C*Real.exp (c*|x|))
    (x a z : ℝ) : |z*f (x+a*z)| ≤ C*Real.exp (c*|x|)*Real.exp ((c*|a|+1)*|z|) := by
  rw [abs_mul]
  calc
    _ ≤ Real.exp |z| * (C*Real.exp (c*|x|)*Real.exp (c*|a| *|z|)) := by
      apply mul_le_mul _ (affine_exp_bound hC hc hb x a z) (abs_nonneg _) (Real.exp_nonneg _)
      have := Real.add_one_le_exp |z|
      linarith
    _ = _ := by rw [show (c*|a|+1)*|z| = |z|+c*|a| *|z| by ring, Real.exp_add]; ring

 theorem ExpBounded.affine_integrable {f : ℝ → ℝ} (hf : ExpBounded f) (x a : ℝ) :
    Integrable (fun z => f (x+a*z)) (gaussianReal 0 1) := by
  obtain ⟨C,c,hC,hc,hb⟩ := hf.2
  apply ((standardGaussian_exp_abs_integrable (c*|a|)).const_mul (C*Real.exp (c*|x|))).mono'
    (hf.1.comp (continuous_const.add (continuous_const.mul continuous_id))).aestronglyMeasurable
  exact Eventually.of_forall fun z => by
    change |f (x+a*z)| ≤ _
    exact affine_exp_bound hC hc hb x a z

 theorem ExpBounded.affine_z_integrable {f : ℝ → ℝ} (hf : ExpBounded f) (x a : ℝ) :
    Integrable (fun z => z*f (x+a*z)) (gaussianReal 0 1) := by
  obtain ⟨C,c,hC,hc,hb⟩ := hf.2
  apply ((standardGaussian_exp_abs_integrable (c*|a|+1)).const_mul (C*Real.exp (c*|x|))).mono'
    (continuous_id.mul (hf.1.comp (continuous_const.add (continuous_const.mul continuous_id)))).aestronglyMeasurable
  exact Eventually.of_forall fun z => by
    change |z*f (x+a*z)| ≤ _
    exact affine_z_exp_bound hC hc hb x a z

 

 theorem hasDerivAt_gaussian_affine {f f₁ : ℝ → ℝ}
    (hf : ExpBounded f) (hf₁ : ExpBounded f₁)
    (hd : ∀ y, HasDerivAt f (f₁ y) y) (x a : ℝ) :
    HasDerivAt (fun t => ∫ z, f (x+t*z) ∂gaussianReal 0 1)
      (∫ z, z*f₁ (x+a*z) ∂gaussianReal 0 1) a := by
  obtain ⟨C,c,hC,hc,hb⟩ := hf₁.2
  apply (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (s := Metric.ball a 1) (bound := fun z => C*Real.exp (c*|x|)*Real.exp ((c*(|a|+1)+1)*|z|))
    (Metric.ball_mem_nhds a (by norm_num)) _ (hf.affine_integrable x a) _ _ _ _).2
  · exact Eventually.of_forall fun t =>
      (hf.1.comp (continuous_const.add (continuous_const.mul continuous_id))).aestronglyMeasurable
  · exact (continuous_id.mul (hf₁.1.comp (continuous_const.add
      (continuous_const.mul continuous_id)))).aestronglyMeasurable
  · apply Eventually.of_forall
    intro z t ht
    have hat : |t| ≤ |a|+1 := by
      have h := (Metric.mem_ball.mp ht).le
      rw [Real.dist_eq] at h
      calc |t| = |(t-a)+a| := by congr 1; ring
           _ ≤ |t-a|+|a| := abs_add_le _ _
           _ ≤ |a|+1 := by linarith
    change |z*f₁ (x+t*z)| ≤ _
    exact (affine_z_exp_bound hC hc hb x t z).trans (by gcongr)
  · exact (standardGaussian_exp_abs_integrable _).const_mul _
  · exact Eventually.of_forall fun z t _ =>
      ((hd (x+t*z)).comp t ((hasDerivAt_id t).mul_const z |>.const_add x)).congr_deriv (by ring)

 

 theorem hasDerivAt_gaussian_affine_heat {f f₁ f₂ : ℝ → ℝ}
    (hf : ExpBounded f) (hf₁ : ExpBounded f₁) (hf₂ : ExpBounded f₂)
    (hd : ∀ y, HasDerivAt f (f₁ y) y) (hd₁ : ∀ y, HasDerivAt f₁ (f₂ y) y)
    (x a : ℝ) :
    HasDerivAt (fun t => ∫ z, f (x+t*z) ∂gaussianReal 0 1)
      (a * ∫ z, f₂ (x+a*z) ∂gaussianReal 0 1) a := by
  have hs := standardGaussian_stein
    (f := fun z => f₁ (x+a*z)) (f₁ := fun z => a*f₂ (x+a*z))
    (fun z => ((hd₁ (x+a*z)).comp z ((hasDerivAt_id z).const_mul a |>.const_add x)).congr_deriv (by ring))
    (hf₁.affine_integrable x a) ((hf₂.affine_integrable x a).const_mul a)
    (hf₁.affine_z_integrable x a)
  rw [integral_const_mul] at hs
  simpa only [hs] using hasDerivAt_gaussian_affine hf hf₁ hd x a

 theorem hasDerivAt_gaussian_variance {f f₁ f₂ : ℝ → ℝ}
    (hf : ExpBounded f) (hf₁ : ExpBounded f₁) (hf₂ : ExpBounded f₂)
    (hd : ∀ y, HasDerivAt f (f₁ y) y) (hd₁ : ∀ y, HasDerivAt f₁ (f₂ y) y)
    (x : ℝ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s => ∫ z, f (x+Real.sqrt s*z) ∂gaussianReal 0 1)
      ((1/2:ℝ) * ∫ z, f₂ (x+Real.sqrt t*z) ∂gaussianReal 0 1) t := by
  have h := (hasDerivAt_gaussian_affine_heat hf hf₁ hf₂ hd hd₁ x (Real.sqrt t)).comp t
    (Real.hasDerivAt_sqrt ht.ne')
  exact h.congr_deriv (by field_simp [Real.sqrt_ne_zero'.mpr ht])

end SKFluctuations.GaussianCalculus

namespace SKFluctuations.GaussianCalculus
open MeasureTheory ProbabilityTheory Hierarchy
open scoped Topology NNReal

 theorem ExpBounded.exp_lipschitz {F : ℝ → ℝ} {C : ℝ≥0}
    (hF : LipschitzWith C F) (m : ℝ) : ExpBounded (fun x => Real.exp (m*F x)) := by
  refine ⟨(Real.continuous_exp.comp (hF.continuous.const_mul m)),
    Real.exp (m*F 0), |m| * C, (Real.exp_nonneg _), mul_nonneg (abs_nonneg _) C.coe_nonneg, ?_⟩
  intro x
  rw [abs_of_pos (Real.exp_pos _), ← Real.exp_add, Real.exp_le_exp]
  have ht : |F x-F 0| ≤ C*|x| := by simpa only [Real.dist_eq, sub_zero] using hF.dist_le_mul x 0
  have hm := le_abs_self (m*(F x-F 0))
  rw [abs_mul] at hm
  have h := mul_le_mul_of_nonneg_left ht (abs_nonneg m)
  nlinarith

 theorem ExpBounded.of_lipschitz {F : ℝ → ℝ} {C : ℝ≥0}
    (hF : LipschitzWith C F) : ExpBounded F := by
  refine ⟨hF.continuous, |F 0|+C, 1, by positivity, by norm_num, ?_⟩
  intro x
  have ht : |F x-F 0| ≤ C*|x| := by simpa only [Real.dist_eq, sub_zero] using hF.dist_le_mul x 0
  have he : |x| ≤ Real.exp |x| := by have := Real.add_one_le_exp |x|; linarith
  have he1 : 1 ≤ Real.exp |x| := Real.one_le_exp (abs_nonneg x)
  calc
    |F x| ≤ |F x-F 0|+|F 0| := by simpa using abs_add_le (F x-F 0) (F 0)
    _ ≤ C*|x|+|F 0| := by linarith
    _ ≤ C*Real.exp |x|+|F 0| * Real.exp |x| := add_le_add
      (mul_le_mul_of_nonneg_left he C.coe_nonneg) (by nlinarith [abs_nonneg (F 0)])
    _ = (|F 0|+C)*Real.exp (1*|x|) := by ring_nf

 theorem ExpBounded.bdd_mul {f A : ℝ → ℝ} (hf : ExpBounded f)
    (hA : BddSmooth 0 A) : ExpBounded (fun x => A x*f x) := by
  obtain ⟨C,c,hC,hc,hb⟩ := hf.2
  obtain ⟨B,hB,hbB⟩ := hA.bound
  refine ⟨hA.continuous.mul hf.1, B*C, c, mul_nonneg hB hC, hc, fun x => ?_⟩
  rw [abs_mul]
  exact (mul_le_mul (hbB x) (hb x) (abs_nonneg _) hB).trans_eq (by ring)

 

 theorem hasDerivAt_scalar_heat_continuation {F F₁ F₂ : ℝ → ℝ} {C : ℝ≥0}
    (hF : LipschitzWith C F) (hF₁ : BddSmooth 0 F₁) (hF₂ : BddSmooth 0 F₂)
    (hd : ∀ y, HasDerivAt F (F₁ y) y) (hd₁ : ∀ y, HasDerivAt F₁ (F₂ y) y)
    {m t : ℝ} (hm : m ≠ 0) (ht : 0 < t) (x : ℝ) :
    HasDerivAt (fun s => Real.log (∫ z, Real.exp (m*F (x+Real.sqrt s*z)) ∂gaussianReal 0 1)/m)
      ((1/2:ℝ)*(tiltedMean (gaussianReal 0 1) m (fun z => F (x+Real.sqrt t*z))
          (fun z => F₂ (x+Real.sqrt t*z)) + m *
        tiltedMean (gaussianReal 0 1) m (fun z => F (x+Real.sqrt t*z))
          (fun z => (F₁ (x+Real.sqrt t*z))^2))) t := by
  let P : ℝ → ℝ := fun y => Real.exp (m*F y)
  let P₁ : ℝ → ℝ := fun y => m*F₁ y*P y
  let P₂ : ℝ → ℝ := fun y => (m*F₂ y + m^2*(F₁ y)^2)*P y
  have hP : ExpBounded P := ExpBounded.exp_lipschitz hF m
  have hB₁ : BddSmooth 0 (fun y => m*F₁ y) := hF₁.const_mul m
  have hB₂ : BddSmooth 0 (fun y => m*F₂ y + m^2*(F₁ y)^2) := by
    simpa only [pow_two] using (hF₂.const_mul m).add ((hF₁.mul hF₁).const_mul (m*m))
  have hdP (y : ℝ) : HasDerivAt P (P₁ y) y := by
    exact ((hd y).const_mul m |>.exp).congr_deriv (by dsimp [P₁,P]; ring)
  have hdP₁ (y : ℝ) : HasDerivAt P₁ (P₂ y) y := by
    exact (((hd₁ y).const_mul m).mul (hdP y)).congr_deriv (by dsimp [P₂,P₁]; ring)
  have h := hasDerivAt_gaussian_variance hP (hP.bdd_mul hB₁) (hP.bdd_mul hB₂) hdP hdP₁ x ht
  have hi := hP.affine_integrable x (Real.sqrt t)
  have hp : 0 < ∫ z, P (x+Real.sqrt t*z) ∂gaussianReal 0 1 := partition_pos m hi
  have hF₁sq : BddSmooth 0 (fun y => (F₁ y)^2) := by simpa only [pow_two] using hF₁.mul hF₁
  have hi₂ : Integrable (fun z => F₂ (x+Real.sqrt t*z)*P (x+Real.sqrt t*z)) (gaussianReal 0 1) :=
    (hP.bdd_mul hF₂).affine_integrable x (Real.sqrt t)
  have hi₁sq : Integrable (fun z => (F₁ (x+Real.sqrt t*z))^2*P (x+Real.sqrt t*z)) (gaussianReal 0 1) :=
    (hP.bdd_mul hF₁sq).affine_integrable x (Real.sqrt t)
  have he : (∫ z, P₂ (x+Real.sqrt t*z) ∂gaussianReal 0 1) =
      m*(∫ z, F₂ (x+Real.sqrt t*z)*P (x+Real.sqrt t*z) ∂gaussianReal 0 1) +
      m^2*(∫ z, (F₁ (x+Real.sqrt t*z))^2*P (x+Real.sqrt t*z) ∂gaussianReal 0 1) := by
    rw [← integral_const_mul, ← integral_const_mul, ← integral_add (hi₂.const_mul m) (hi₁sq.const_mul (m^2))]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun z => by dsimp [P₂]; ring
  apply ((h.log hp.ne').div_const m).congr_deriv
  rw [he]
  dsimp [tiltedMean,P]
  field_simp

end SKFluctuations.GaussianCalculus

namespace SKFluctuations.GaussianCalculus
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal

 

theorem ExpBounded.continuous_gaussian_affine {f : ℝ → ℝ} (hf : ExpBounded f) (x : ℝ) :
    Continuous (fun a => ∫ z, f (x+a*z) ∂gaussianReal 0 1) := by
  obtain ⟨C,c,hC,hc,hb⟩ := hf.2
  apply continuous_iff_continuousAt.mpr
  intro a
  apply continuousAt_of_dominated
    (bound := fun z => C*Real.exp (c*|x|)*Real.exp (c*(|a|+1)*|z|))
  · exact Eventually.of_forall fun t =>
      (hf.1.comp (continuous_const.add (continuous_const.mul continuous_id))).aestronglyMeasurable
  · filter_upwards [Metric.ball_mem_nhds a (by norm_num : (0:ℝ)<1)] with t ht
    apply Eventually.of_forall
    intro z
    have hat : |t| ≤ |a|+1 := by
      have h := (Metric.mem_ball.mp ht).le
      rw [Real.dist_eq] at h
      calc |t| = |(t-a)+a| := by congr 1; ring
           _ ≤ |t-a|+|a| := abs_add_le _ _
           _ ≤ |a|+1 := by linarith
    change |f (x+t*z)| ≤ _
    exact (affine_exp_bound hC hc hb x t z).trans (by gcongr)
  · exact (standardGaussian_exp_abs_integrable _).const_mul _
  · exact Eventually.of_forall fun z =>
      (hf.1.comp (continuous_const.add (continuous_id.mul_const z))).continuousAt

theorem ExpBounded.continuous_gaussian_variance {f : ℝ → ℝ} (hf : ExpBounded f) (x : ℝ) :
    Continuous (fun s => ∫ z, f (x+Real.sqrt s*z) ∂gaussianReal 0 1) :=
  (hf.continuous_gaussian_affine x).comp Real.continuous_sqrt

 

theorem hasDerivWithinAt_gaussian_variance_zero {f f₁ f₂ : ℝ → ℝ}
    (hf : ExpBounded f) (hf₁ : ExpBounded f₁) (hf₂ : ExpBounded f₂)
    (hd : ∀ y, HasDerivAt f (f₁ y) y) (hd₁ : ∀ y, HasDerivAt f₁ (f₂ y) y) (x : ℝ) :
    HasDerivWithinAt (fun s => ∫ z, f (x+Real.sqrt s*z) ∂gaussianReal 0 1)
      ((1/2:ℝ)*f₂ x) (Ici 0) 0 := by
  apply hasDerivWithinAt_Ici_of_tendsto_deriv (s := Ioi 0)
  · exact fun s hs => (hasDerivAt_gaussian_variance hf hf₁ hf₂ hd hd₁ x hs).differentiableAt.differentiableWithinAt
  · exact (hf.continuous_gaussian_variance x).continuousAt.continuousWithinAt
  · exact self_mem_nhdsWithin
  · have hlim : Tendsto (fun s => (1/2:ℝ)*(∫ z, f₂ (x+Real.sqrt s*z) ∂gaussianReal 0 1))
        (𝓝[>] (0:ℝ)) (𝓝 ((1/2:ℝ)*(∫ z, f₂ (x+Real.sqrt 0*z) ∂gaussianReal 0 1))) :=
      ((hf₂.continuous_gaussian_variance x).const_mul (1/2:ℝ)).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    have he : (fun s => deriv (fun r => ∫ z, f (x+Real.sqrt r*z) ∂gaussianReal 0 1) s) =ᶠ[𝓝[>] (0:ℝ)]
        (fun s => (1/2:ℝ)*(∫ z, f₂ (x+Real.sqrt s*z) ∂gaussianReal 0 1)) := by
      filter_upwards [self_mem_nhdsWithin] with s hs
      exact (hasDerivAt_gaussian_variance hf hf₁ hf₂ hd hd₁ x hs).deriv
    have hc : Tendsto (fun s => (1/2:ℝ)*(∫ z, f₂ (x+Real.sqrt s*z) ∂gaussianReal 0 1))
        (𝓝[>] (0:ℝ)) (𝓝 ((1/2:ℝ)*f₂ x)) := by
      simpa only [Real.sqrt_zero, zero_mul, add_zero, integral_const, probReal_univ, one_smul] using hlim
    exact hc.congr' he.symm

theorem hasDerivWithinAt_gaussian_variance {f f₁ f₂ : ℝ → ℝ}
    (hf : ExpBounded f) (hf₁ : ExpBounded f₁) (hf₂ : ExpBounded f₂)
    (hd : ∀ y, HasDerivAt f (f₁ y) y) (hd₁ : ∀ y, HasDerivAt f₁ (f₂ y) y)
    (x : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    HasDerivWithinAt (fun s => ∫ z, f (x+Real.sqrt s*z) ∂gaussianReal 0 1)
      ((1/2:ℝ)*∫ z, f₂ (x+Real.sqrt t*z) ∂gaussianReal 0 1) (Ici 0) t := by
  rcases eq_or_lt_of_le ht with ht | ht
  · subst t
    simpa only [Real.sqrt_zero, zero_mul, add_zero, integral_const, probReal_univ, one_smul]
      using hasDerivWithinAt_gaussian_variance_zero hf hf₁ hf₂ hd hd₁ x
  · exact (hasDerivAt_gaussian_variance hf hf₁ hf₂ hd hd₁ x ht).hasDerivWithinAt

end SKFluctuations.GaussianCalculus

namespace SKFluctuations.Scalar
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal

 def logCosh (x : ℝ) : ℝ := Real.log (Real.cosh x)
 def curvature (x : ℝ) : ℝ := 1-(Real.tanh x)^2
 def third (x : ℝ) : ℝ := -2*Real.tanh x*curvature x
 def fourth (x : ℝ) : ℝ := -2+8*(Real.tanh x)^2-6*(Real.tanh x)^4

 theorem tanh_derivative (x : ℝ) : HasDerivAt Real.tanh (curvature x) x := by
  have hh := (Real.hasDerivAt_sinh x).div (Real.hasDerivAt_cosh x) (ne_of_gt (Real.cosh_pos x))
  rw [show Real.tanh = (fun y => Real.sinh y / Real.cosh y) from funext Real.tanh_eq_sinh_div_cosh]
  apply hh.congr_deriv
  unfold curvature
  rw [Real.tanh_eq_sinh_div_cosh]
  field_simp

 theorem logCosh_derivative (x : ℝ) : HasDerivAt logCosh (Real.tanh x) x := by
  rw [Real.tanh_eq_sinh_div_cosh]
  change HasDerivAt (fun y => Real.log (Real.cosh y)) (Real.sinh x / Real.cosh x) x
  exact
    (Real.hasDerivAt_cosh x).log (ne_of_gt (Real.cosh_pos x))

 theorem curvature_derivative (x : ℝ) : HasDerivAt curvature (third x) x := by
  have hh := (hasDerivAt_const x (1:ℝ)).sub ((tanh_derivative x).pow 2)
  change HasDerivAt (fun y => 1-(Real.tanh y)^2) (third x) x
  apply hh.congr_deriv
  dsimp [third]
  ring

 theorem third_derivative (x : ℝ) : HasDerivAt third (fourth x) x := by
  have hh := ((tanh_derivative x).const_mul (-2)).mul (curvature_derivative x)
  change HasDerivAt (fun y => -2*Real.tanh y*curvature y) (fourth x) x
  apply hh.congr_deriv
  dsimp [third,curvature,fourth]
  ring

 theorem tanh_continuous : Continuous Real.tanh :=
  continuous_iff_continuousAt.mpr fun x => (tanh_derivative x).continuousAt

 theorem curvature_continuous : Continuous curvature :=
  continuous_const.sub (tanh_continuous.pow 2)

 theorem third_continuous : Continuous third :=
  (tanh_continuous.const_mul (-2)).mul curvature_continuous

 theorem fourth_continuous : Continuous fourth :=
  (continuous_const.add ((tanh_continuous.pow 2).const_mul 8)).sub ((tanh_continuous.pow 4).const_mul 6)

 theorem logCosh_lipschitz : LipschitzWith 1 logCosh := by
  apply lipschitzWith_of_nnnorm_deriv_le (fun x => (logCosh_derivative x).differentiableAt)
  intro x
  rw [(logCosh_derivative x).deriv]
  exact_mod_cast (Real.abs_tanh_lt_one x).le

 theorem curvature_bounds (x : ℝ) : 0 ≤ curvature x ∧ curvature x ≤ 1 := by
  unfold curvature
  have hh : (Real.tanh x)^2 ≤ 1 := (sq_le_one_iff_abs_le_one _).mpr (Real.abs_tanh_lt_one x).le
  constructor <;> nlinarith [sq_nonneg (Real.tanh x)]

 theorem logCosh_expBounded : GaussianCalculus.ExpBounded logCosh := by
  have hh := GaussianCalculus.ExpNormBounded.lipschitz logCosh_lipschitz
  simpa only [GaussianCalculus.ExpNormBounded,GaussianCalculus.ExpBounded,Real.norm_eq_abs] using hh

 theorem tanh_expBounded : GaussianCalculus.ExpBounded Real.tanh := by
  refine ⟨tanh_continuous,1,0,by norm_num,le_rfl,?_⟩
  intro x
  simpa only [zero_mul,Real.exp_zero,mul_one] using (Real.abs_tanh_lt_one x).le

 theorem curvature_expBounded : GaussianCalculus.ExpBounded curvature := by
  refine ⟨curvature_continuous,1,0,by norm_num,le_rfl,?_⟩
  intro x
  simpa only [zero_mul,Real.exp_zero,mul_one,abs_of_nonneg (curvature_bounds x).1] using (curvature_bounds x).2

 theorem third_expBounded : GaussianCalculus.ExpBounded third := by
  refine ⟨third_continuous,2,0,by norm_num,le_rfl,?_⟩
  intro x
  simp only [third,abs_mul,abs_of_nonneg (curvature_bounds x).1,zero_mul,Real.exp_zero,mul_one]
  norm_num only [abs_neg,abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
  nlinarith [(mul_le_mul (Real.abs_tanh_lt_one x).le (curvature_bounds x).2
    (curvature_bounds x).1 (by norm_num : (0:ℝ) ≤ 1))]

 theorem fourth_expBounded : GaussianCalculus.ExpBounded fourth := by
  refine ⟨fourth_continuous,16,0,by norm_num,le_rfl,?_⟩
  intro x
  have h₂ : (Real.tanh x)^2 ≤ 1 := (sq_le_one_iff_abs_le_one _).mpr (Real.abs_tanh_lt_one x).le
  have h₄ : (Real.tanh x)^4 ≤ 1 := by nlinarith [sq_nonneg ((Real.tanh x)^2-1),sq_nonneg (Real.tanh x)]
  simp only [zero_mul,Real.exp_zero,mul_one]
  change |(-2+8*(Real.tanh x)^2-6*(Real.tanh x)^4)| ≤ 16
  apply abs_le.mpr
  constructor <;> nlinarith [sq_nonneg (Real.tanh x),pow_nonneg (sq_nonneg (Real.tanh x)) 2]

end SKFluctuations.Scalar

namespace SKFluctuations.Scalar
open MeasureTheory ProbabilityTheory Filter Set GaussianCalculus
open scoped Topology NNReal

noncomputable def rsHeat (t : ℝ) : ℝ := ∫ z, logCosh (Real.sqrt t*z) ∂gaussianReal 0 1
noncomputable def rsHeatSlope (t : ℝ) : ℝ := (1/2:ℝ)*∫ z, curvature (Real.sqrt t*z) ∂gaussianReal 0 1

 theorem rsHeat_derivative {t : ℝ} (ht : 0 ≤ t) :
    HasDerivWithinAt rsHeat (rsHeatSlope t) (Ici 0) t := by
  change HasDerivWithinAt (fun s => ∫ z, logCosh (Real.sqrt s*z) ∂gaussianReal 0 1) _ _ _
  simpa only [rsHeatSlope,zero_add] using
    hasDerivWithinAt_gaussian_variance logCosh_expBounded tanh_expBounded curvature_expBounded
      logCosh_derivative tanh_derivative 0 ht

 theorem rsHeatSlope_derivative_zero :
    HasDerivWithinAt rsHeatSlope (-1/2) (Ici 0) 0 := by
  have hh := (hasDerivWithinAt_gaussian_variance_zero curvature_expBounded third_expBounded
    fourth_expBounded curvature_derivative third_derivative 0).const_mul (1/2:ℝ)
  norm_num only [fourth,Real.tanh_zero,zero_pow (by decide : 2 ≠ 0),zero_pow (by decide : 4 ≠ 0),
    mul_zero,add_zero,sub_zero,zero_add] at hh
  change HasDerivWithinAt (fun s => (1/2:ℝ)*∫ z, curvature (Real.sqrt s*z) ∂gaussianReal 0 1) _ _ _
  exact hh.congr_deriv (by ring)

 theorem rsHeat_zero : rsHeat 0 = 0 := by simp [rsHeat,logCosh]
 theorem rsHeatSlope_zero : rsHeatSlope 0 = 1/2 := by simp [rsHeatSlope,curvature]

noncomputable def rsVariation (T q : ℝ) : ℝ := rsHeat (T*q)-T*q/2+T*q^2/4
noncomputable def rsVariationSlope (T q : ℝ) : ℝ := T*rsHeatSlope (T*q)-T/2+T*q/2

 theorem rsVariation_zero (T : ℝ) : rsVariation T 0 = 0 := by simp [rsVariation,rsHeat_zero]
 theorem rsVariationSlope_zero (T : ℝ) : rsVariationSlope T 0 = 0 := by simp [rsVariationSlope,rsHeatSlope_zero]; ring

 theorem rsVariation_derivative {T q : ℝ} (hT : 0 ≤ T) (hq : 0 ≤ q) :
    HasDerivWithinAt (rsVariation T) (rsVariationSlope T q) (Ici 0) q := by
  have hi := (hasDerivAt_id q).const_mul T
  have hh := (rsHeat_derivative (mul_nonneg hT hq)).comp q hi.hasDerivWithinAt
    (by intro s hs; exact mul_nonneg hT hs)
  have hd := (hh.sub (hi.hasDerivWithinAt.div_const 2)).add
    (((hasDerivWithinAt_id q (Ici 0)).pow 2).const_mul T |>.div_const 4)
  change HasDerivWithinAt (fun s => rsHeat (T*s)-T*s/2+T*s^2/4) _ _ _
  apply hd.congr_deriv
  dsimp [rsVariationSlope]
  ring

 theorem rsVariationSlope_derivative_zero {T : ℝ} (hT : 0 ≤ T) :
    HasDerivWithinAt (rsVariationSlope T) ((T-T^2)/2) (Ici 0) 0 := by
  have hi := (hasDerivAt_id (0:ℝ)).const_mul T
  have hh := (by simpa only [mul_zero] using rsHeatSlope_derivative_zero :
    HasDerivWithinAt rsHeatSlope (-1/2) (Ici 0) (T*0)).comp 0 hi.hasDerivWithinAt
      (by intro s hs; exact mul_nonneg hT hs)
  have hd := ((hh.const_mul T).sub_const (T/2)).add (hi.hasDerivWithinAt.div_const 2)
  change HasDerivWithinAt (fun s => T*rsHeatSlope (T*s)-T/2+T*s/2) _ _ _
  apply hd.congr_deriv
  ring

end SKFluctuations.Scalar

namespace SKFluctuations.Scalar
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal

 

theorem rsVariation_strictly_negative {T : ℝ} (hT : 1 < T) :
    ∃ δ > 0, ∀ q ∈ Ioo (0:ℝ) δ, rsVariation T q < 0 := by
  have hT0 : 0 ≤ T := by linarith
  have hn : (T-T^2)/2 < 0 := by nlinarith
  have hh := (rsVariationSlope_derivative_zero hT0).Ioi_of_Ici.limsup_slope_le'
    (lt_irrefl (0:ℝ)) hn
  change ∀ᶠ q in 𝓝[>] (0:ℝ), slope (rsVariationSlope T) 0 q < 0 at hh
  obtain ⟨δ,hδ,hd⟩ := Metric.mem_nhdsWithin_iff.mp hh
  refine ⟨δ,hδ,?_⟩
  intro q hq
  have hneg (r : ℝ) (hr : r ∈ Ioo (0:ℝ) q) : rsVariationSlope T r < 0 := by
    have hh := hd (show r ∈ Metric.ball (0:ℝ) δ ∩ Ioi 0 from
      ⟨by simpa only [Metric.mem_ball,Real.dist_eq,sub_zero,abs_of_pos hr.1] using hr.2.trans hq.2,hr.1⟩)
    change slope (rsVariationSlope T) 0 r < 0 at hh
    rw [slope_def_field,rsVariationSlope_zero,sub_zero,sub_zero] at hh
    simpa only [zero_mul] using (div_lt_iff₀ hr.1).mp hh
  have hc : ContinuousOn (rsVariation T) (Icc 0 q) := by
    intro r hr
    exact (rsVariation_derivative hT0 hr.1).continuousWithinAt.mono Icc_subset_Ici_self
  obtain ⟨r,hr,he⟩ := exists_hasDerivAt_eq_slope (rsVariation T) (rsVariationSlope T) hq.1 hc
    (fun r hr => (rsVariation_derivative hT0 hr.1.le).hasDerivAt (Ici_mem_nhds hr.1))
  rw [rsVariation_zero,sub_zero,sub_zero] at he
  have hh := hneg r hr
  rw [he] at hh
  simpa only [zero_mul] using (div_lt_iff₀ hq.1).mp hh

end SKFluctuations.Scalar

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal BigOperators

 

def diracMassProfile (q : ℝ) : boundedMassProfiles := ⟨(fun s => if s < q then 0 else 1),by
  constructor
  · intro s
    change (if s < q then (0:ℝ) else 1) ∈ Icc 0 1
    split_ifs <;> norm_num
  · intro s t hst
    change (if s < q then (0:ℝ) else 1) ≤ (if t < q then 0 else 1)
    split_ifs <;> norm_num at *
    linarith⟩

 theorem diracMassProfile_mem {q : ℝ} (hq : q ∈ Icc (0:ℝ) 1) : diracMassProfile q ∈ scalarProfiles := by
  constructor
  · intro s hs
    exact ite_eq_left (hs.trans_le hq.1)
  · intro s hs
    exact ite_eq_right (not_lt.mpr (hq.2.trans hs.le))

 theorem scalarPenalty_dirac {q : ℝ} (hq : q ∈ Icc (0:ℝ) 1) :
    scalarPenalty (diracMassProfile q) = (1-q^2)/2 := by
  unfold scalarPenalty
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (weightedProfile_monotone (diracMassProfile q)).intervalIntegrable
    (weightedProfile_monotone (diracMassProfile q)).intervalIntegrable]
  have hl : (∫ s in (0:ℝ)..q, weightedProfile (diracMassProfile q) s) = 0 := by
    calc
      _ = ∫ s in (0:ℝ)..q, (0:ℝ) := by
        apply intervalIntegral.integral_congr_Ioo_of_le hq.1
        intro s hs
        simp only [weightedProfile,diracMassProfile,ite_eq_left hs.2,mul_zero]
      _ = 0 := by simp
  have hr : (∫ s in q..(1:ℝ), weightedProfile (diracMassProfile q) s) = (1-q^2)/2 := by
    calc
      _ = ∫ s in q..(1:ℝ), s := by
        apply intervalIntegral.integral_congr_Ioo_of_le hq.2
        intro s hs
        simp only [weightedProfile,diracMassProfile,ite_eq_right (not_lt.mpr hs.1.le),
          max_eq_left (hq.1.trans hs.1.le),mul_one]
      _ = (1-q^2)/2 := by rw [integral_id]; norm_num
  rw [hl,hr,zero_add]

 theorem scalarRoot_mass_one (u v : ℝ≥0) :
    zeroContinuation (Measure.pi fun _ : Fin 1 => gaussianReal 0 u)
      (clockContinuation 1 scalarTerminal.F v) 0 = Scalar.rsHeat u+(v:ℝ)/2 := by
  unfold zeroContinuation
  simp only [zero_add,scalarTerminal_mass_one]
  rw [← integral_isotropicGaussian u (f := fun z : Fin 1 → ℝ => Real.log (Real.cosh (z 0))+(v:ℝ)/2)
    (by exact (Scalar.logCosh_lipschitz.continuous.comp (continuous_apply 0)).add_const _)]
  simp only [Pi.smul_apply,smul_eq_mul]
  rw [integral_gaussian_eval (ι := Fin 1) (0:Fin 1) 1
    (f := fun y => Real.log (Real.cosh (Real.sqrt (u:ℝ)*y))+(v:ℝ)/2)
      (by exact (Scalar.logCosh_lipschitz.continuous.comp (continuous_const.mul continuous_id)).add_const _)]
  have hi : Integrable (fun y => Real.log (Real.cosh (Real.sqrt (u:ℝ)*y))) (gaussianReal 0 1) := by
    simpa only [zero_add,Scalar.logCosh] using Scalar.logCosh_expBounded.affine_integrable 0 (Real.sqrt (u:ℝ))
  rw [integral_add hi (integrable_const _),integral_const]
  simp [Scalar.rsHeat,Scalar.logCosh]

end SKFluctuations.Hierarchy

end

end OAI
