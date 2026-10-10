import Mathlib
import OAI.Probability.ParisiFinite.PartitionSite

namespace OAI

/-! Abs Mul Exp Le. -/

noncomputable section

open scoped BigOperators ComplexConjugate InnerProductSpace Topology ComplexOrder
open Filter
open scoped BigOperators
open scoped Matrix Matrix.Norms.L2Operator ComplexConjugate
open scoped InnerProductSpace ComplexConjugate
open Filter Topology
open Filter Set Topology
open scoped InnerProductSpace ComplexConjugate Topology
open scoped InnerProductSpace
open scoped BigOperators Topology InnerProductSpace
open scoped BigOperators InnerProductSpace
open scoped BigOperators Matrix Topology ComplexConjugate
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology
open scoped BigOperators Matrix Topology
open scoped BigOperators Matrix Topology Matrix.Norms.Operator
open scoped Topology
open Filter Asymptotics
open scoped InnerProductSpace Topology
open scoped InnerProductSpace BigOperators
open scoped InnerProductSpace Topology BigOperators
open scoped Topology BigOperators
open scoped Matrix Matrix.Norms.L2Operator InnerProductSpace
open scoped Matrix Matrix.Norms.L2Operator InnerProductSpace BigOperators
open Filter ContinuousLinearMap
open ContinuousLinearMap
open scoped InnerProductSpace BigOperators Topology
open ContinuousLinearMap InnerProductSpace
open ContinuousLinearMap Filter
open Filter MeasureTheory
open scoped Topology ENNReal
open MeasureTheory ProbabilityTheory
open scoped BigOperators Topology RealInnerProductSpace
open scoped BigOperators TensorProduct
open scoped Topology InnerProductSpace
open MeasureTheory Filter
open MeasureTheory ProbabilityTheory Complex
open scoped BigOperators Topology InnerProductSpace ComplexConjugate
open scoped BigOperators Topology NNReal
open scoped BigOperators NNReal Topology
open scoped BigOperators NNReal
open scoped NNReal Topology
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology
namespace ParisiFinite

lemma abs_mul_exp_le (c z : ℝ) :
    |z| * Real.exp (c*|z|) ≤ Real.exp ((c+1)*|z|) := by
  have hz : |z| ≤ Real.exp |z| := by linarith [Real.add_one_le_exp |z|]
  calc
    _ ≤ Real.exp |z| * Real.exp (c*|z|) := mul_le_mul_of_nonneg_right hz (Real.exp_pos _).le
    _ = Real.exp ((c+1)*|z|) := by rw [← Real.exp_add]; congr 1; ring

lemma exp_scale_near_le {L : ℝ≥0} {f : ℝ → ℝ} (hf : LipschitzWith L f)
    (a x s₀ : ℝ) {s : ℝ} (hs : |s-s₀| ≤ 1) (z : ℝ) :
    Real.exp (a*f (x+s*z)) ≤
      Real.exp (|a| * |f x|)*Real.exp ((|a| * L*(|s₀|+1))*|z|) := by
  have hss : |s| ≤ |s₀|+1 := by
    have ht := abs_add_le (s-s₀) s₀
    rw [sub_add_cancel] at ht
    linarith
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hb := shift_norm_le hf x s z
  have hmul := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hss L.coe_nonneg) (abs_nonneg z)
  calc
    a*f (x+s*z) ≤ |a| * |f (x+s*z)| := by simpa only [abs_mul] using le_abs_self (a*f (x+s*z))
    _ ≤ |a| * (|f x|+(L:ℝ)*(|s₀|+1)*|z|) := mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg a)
    _ = _ := by ring

lemma coord_exp_scale_near_le {L : ℝ≥0} {f : ℝ → ℝ} (hf : LipschitzWith L f)
    (a x s₀ : ℝ) {s : ℝ} (hs : |s-s₀| ≤ 1) (z : ℝ) :
    |z| * Real.exp (a*f (x+s*z)) ≤
      Real.exp (|a| * |f x|)*Real.exp ((|a| * L*(|s₀|+1)+1)*|z|) := by
  calc
    _ ≤ |z| * (Real.exp (|a| * |f x|)*Real.exp ((|a| * L*(|s₀|+1))*|z|)) :=
      mul_le_mul_of_nonneg_left (exp_scale_near_le hf a x s₀ hs z) (abs_nonneg z)
    _ = Real.exp (|a| * |f x|)*(|z| * Real.exp ((|a| * L*(|s₀|+1))*|z|)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (abs_mul_exp_le _ z) (Real.exp_pos _).le

lemma integrable_coord_exp_weight {L : ℝ≥0} {f g : ℝ → ℝ} (hf : LipschitzWith L f)
    (hg : Continuous g) {M : ℝ≥0} (hM : ∀ x, |g x| ≤ M) (a s x : ℝ) :
    Integrable (fun z => z*(Real.exp (a*f (x+s*z))*g (x+s*z))) (gaussianReal 0 1) := by
  have hc := hf.continuous
  apply (((integrable_exp_abs _).const_mul (Real.exp (|a| * |f x|))).mul_const (M:ℝ)).mono'
    (by fun_prop)
  exact ae_of_all _ fun z => by
    simp only [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
    rw [← mul_assoc]
    exact mul_le_mul (coord_exp_scale_near_le hf a x s (by simp) z) (hM _)
      (abs_nonneg _) (by positivity)

lemma hasDerivAt_scale_expMass (f : SmoothField) (a s x : ℝ) :
    HasDerivAt (fun r => expMass a r f.val x)
      (∫ z, a * (z*(Real.exp (a*f.val (x+s*z))*f.d1 (x+s*z))) ∂gaussianReal 0 1) s := by
  have hc := f.continuousVal
  have hc₁ := f.continuousD1
  apply (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (s := Metric.ball s 1)
    (bound := fun z => (Real.exp (|a| * |f.val x|)*
      Real.exp ((|a| * f.bound1*(|s|+1)+1)*|z|)) * (|a| * f.bound1))
    (F' := fun r z => a * (z*(Real.exp (a*f.val (x+r*z))*f.d1 (x+r*z))))
    (Metric.ball_mem_nhds _ (by norm_num)) ?_ (integrable_exp_shift f.lipschitz a x s)
    (by fun_prop) ?_ ?_ ?_).2
  · exact Eventually.of_forall fun _ => by fun_prop
  · exact ae_of_all _ fun z r hr => by
      simp only [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
      have he : |a| * (|z| * (Real.exp (a*f.val (x+r*z))*|f.d1 (x+r*z)|)) =
          (|z| * Real.exp (a*f.val (x+r*z)))*(|a| * |f.d1 (x+r*z)|) := by ring
      rw [he]
      apply mul_le_mul (coord_exp_scale_near_le f.lipschitz a x s
        (by simpa [Real.dist_eq] using hr.le) z)
      · exact mul_le_mul_of_nonneg_left (f.normD1 _) (abs_nonneg _)
      · positivity
      · positivity
  · exact ((integrable_exp_abs _).const_mul _).mul_const _
  · exact ae_of_all _ fun z r _ => by
      have h := ((f.hasD1 (x+r*z)).comp r (((hasDerivAt_id r).mul_const z).const_add x)).const_mul a
      convert h.exp using 1 <;> first | rfl | (simp only [Function.comp_apply, id_eq, one_mul]; ring)

lemma hasDerivAt_scale_average (f : SmoothField) (s x : ℝ) :
    HasDerivAt (fun r => ∫ z, f.val (x+r*z) ∂gaussianReal 0 1)
      (∫ z, z*f.d1 (x+s*z) ∂gaussianReal 0 1) s := by
  have hc := f.continuousVal
  have hc₁ := f.continuousD1
  apply (hasDerivAt_integral_of_dominated_loc_of_deriv_le (s := Set.univ)
    (bound := fun z => |z| * (f.bound1:ℝ)) (F' := fun r z => z*f.d1 (x+r*z))
    univ_mem ?_ (integrable_shift f.lipschitz x s) (by fun_prop) ?_
    (SKQAOA.integrable_abs_standard.mul_const _) ?_).2
  · exact Eventually.of_forall fun _ => by fun_prop
  · exact ae_of_all _ fun z r _ => by
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul_of_nonneg_left (f.normD1 _) (abs_nonneg _)
  · exact ae_of_all _ fun z r _ => by
      convert (f.hasD1 (x+r*z)).comp r (((hasDerivAt_id r).mul_const z).const_add x) using 1 <;>
        first | rfl | (simp only [one_mul]; ring)

 

lemma gaussian_tilt_ibp (f : SmoothField) (a s x : ℝ) :
    (∫ z, z*(Real.exp (a*f.val (x+s*z))*f.d1 (x+s*z)) ∂gaussianReal 0 1) =
      s * (expMoment a s f.val f.d2 x + a*expMoment a s f.val (fun y => f.d1 y^2) x) := by
  let G : ℝ → ℝ := fun z => Real.exp (a*f.val (x+s*z))*f.d1 (x+s*z)
  let G' : ℝ → ℝ := fun z => s*(Real.exp (a*f.val (x+s*z))*(f.d2 (x+s*z)+a*f.d1 (x+s*z)^2))
  have hD : ∀ z, HasDerivAt G (G' z) z := by
    intro z
    have h₁ := (f.hasD1 (x+s*z)).comp z (((hasDerivAt_id z).const_mul s).const_add x)
    have h₂ := (f.hasD2 (x+s*z)).comp z (((hasDerivAt_id z).const_mul s).const_add x)
    convert ((h₁.const_mul a).exp.mul h₂) using 1 <;>
      first | rfl | (dsimp [G']; ring)
  have hi := integrable_exp_weight f.lipschitz f.continuousD1 f.normD1 a s x
  have hi₂ := integrable_exp_weight f.lipschitz f.continuousD2 f.normD2 a s x
  have hs := integrable_exp_weight f.lipschitz (g := fun y => f.d1 y^2)
    (by have hc := f.continuousD1; fun_prop) (sq_bound f.normD1) a s x
  have hi' : Integrable G' (gaussianReal 0 1) := by
    convert (hi₂.add (hs.const_mul a)).const_mul s using 1
    funext z
    dsimp [G']
    ring
  have he := SKGaussian.integral_mul_eq_integral_deriv hD hi hi'
    (integrable_coord_exp_weight f.lipschitz f.continuousD1 f.normD1 a s x)
  change (∫ z, z*G z ∂gaussianReal 0 1) = _
  rw [he]
  have heq : G' = fun z => s *
      (Real.exp (a*f.val (x+s*z))*f.d2 (x+s*z) +
        a*(Real.exp (a*f.val (x+s*z))*f.d1 (x+s*z)^2)) := by
    funext z
    dsimp [G']
    ring
  rw [heq, integral_const_mul, integral_add hi₂ (hs.const_mul a), integral_const_mul]
  rfl

end ParisiFinite

 

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology
namespace ParisiFinite

 

lemma hasDerivAt_step_scale (f : SmoothField) (a s x : ℝ) :
    HasDerivAt (fun r => step a r f.val x)
      (s*(tiltedMean a s f.val f.d2 x + a*tiltedMean a s f.val (fun y => f.d1 y^2) x)) s := by
  by_cases ha : a = 0
  · subst a
    have h := hasDerivAt_scale_average f s x
    have hb := gaussian_tilt_ibp f 0 s x
    simp only [zero_mul, Real.exp_zero, one_mul, add_zero, expMoment] at hb
    rw [hb] at h
    simpa only [step, logMean_zero, tiltedMean_zero, zero_mul, add_zero] using h
  · have h := ((hasDerivAt_scale_expMass f a s x).log
        (expMass_pos f.lipschitz a s x).ne').div_const a
    rw [integral_const_mul, gaussian_tilt_ibp] at h
    have he : (a*(s*(expMoment a s f.val f.d2 x + a*expMoment a s f.val (fun y => f.d1 y^2) x)) /
        expMass a s f.val x) / a =
        s*(tiltedMean a s f.val f.d2 x + a*tiltedMean a s f.val (fun y => f.d1 y^2) x) := by
      unfold tiltedMean
      field_simp
    rw [he] at h
    have hs : (fun r => step a r f.val x) =
        (fun r => Real.log (expMass a r f.val x) / a) := by
      funext r
      simp [step, logMean, ha, expMass]
    rw [hs]
    exact h

lemma hasDerivAt_transform_scale (f : SmoothField) (a s x : ℝ) :
    HasDerivAt (fun r => (f.transform a r).val x)
      (s*((f.transform a s).d2 x + a*((f.transform a s).d1 x)^2)) s := by
  convert hasDerivAt_step_scale f a s x using 1 <;>
    first | rfl | (dsimp [SmoothField.transform]; ring)

 

def fieldOnInterval (f : SmoothField) (a b t : ℝ) : SmoothField :=
  f.transform a (Real.sqrt (b-t))

 

lemma hasDerivAt_fieldOnInterval_time (f : SmoothField) (a b t x : ℝ) (ht : t < b) :
    HasDerivAt (fun r => (fieldOnInterval f a b r).val x)
      (-(1/2 : ℝ)*((fieldOnInterval f a b t).d2 x +
        a*((fieldOnInterval f a b t).d1 x)^2)) t := by
  have hb : 0 < b-t := sub_pos.mpr ht
  have hs := (((hasDerivAt_id t).const_sub b).sqrt (ne_of_gt hb))
  have h := (hasDerivAt_transform_scale f a (Real.sqrt (b-t)) x).comp t hs
  convert h using 1 <;>
    first | rfl | (dsimp [fieldOnInterval]; field_simp)

@[simp] lemma fieldOnInterval_right (f : SmoothField) (a b x : ℝ) :
    (fieldOnInterval f a b b).val x = f.val x := by
  by_cases ha : a = 0
  · simp [fieldOnInterval, SmoothField.transform, step, logMean, ha]
  · simp [fieldOnInterval, SmoothField.transform, step, logMean, ha]

lemma fieldOnInterval_spatial1 (f : SmoothField) (a b t x : ℝ) :
    HasDerivAt (fieldOnInterval f a b t).val ((fieldOnInterval f a b t).d1 x) x :=
  (fieldOnInterval f a b t).hasD1 x

lemma fieldOnInterval_spatial2 (f : SmoothField) (a b t x : ℝ) :
    HasDerivAt (fieldOnInterval f a b t).d1 ((fieldOnInterval f a b t).d2 x) x :=
  (fieldOnInterval f a b t).hasD2 x

 
lemma fieldOnInterval_terminal (β : ℝ≥0) (hβ : 0 < β) (a b x : ℝ) :
    (fieldOnInterval (terminalField β hβ) a b b).val x =
      Real.log (2*Real.cosh ((β:ℝ)*x)) / β := by
  rw [fieldOnInterval_right]
  rfl

end ParisiFinite

 

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology
namespace ParisiFinite

section Ambient
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

 
def ambientStep (a : ℝ) (c : E) (f : E → ℝ) (x : E) : ℝ :=
  logMean (gaussianReal 0 1) a (fun z => f (x+z • c))

def ambientMass (a : ℝ) (c : E) (f : E → ℝ) (x : E) : ℝ :=
  ∫ z, Real.exp (a*f (x+z • c)) ∂gaussianReal 0 1

def ambientMoment (a : ℝ) (c : E) (f g : E → ℝ) (x : E) : ℝ :=
  ∫ z, Real.exp (a*f (x+z • c))*g (x+z • c) ∂gaussianReal 0 1

def ambientTilt (a : ℝ) (c : E) (f g : E → ℝ) (x : E) : ℝ :=
  ambientMoment a c f g x / ambientMass a c f x

lemma line_lipschitz {L : ℝ≥0} {f : E → ℝ} (hf : LipschitzWith L f) (x c : E) :
    LipschitzWith (L*‖c‖₊) (fun z : ℝ => f (x+z • c)) := by
  rw [lipschitzWith_iff_norm_sub_le]
  intro z w
  have h := hf.norm_sub_le (x+z • c) (x+w • c)
  rw [add_sub_add_left_eq_sub, ← sub_smul, norm_smul] at h
  simpa [NNReal.coe_mul, mul_comm, mul_left_comm, mul_assoc] using h

lemma integrable_ambient {L : ℝ≥0} {f : E → ℝ} (hf : LipschitzWith L f) (x c : E) :
    Integrable (fun z : ℝ => f (x+z • c)) (gaussianReal 0 1) := by
  simpa only [zero_add, one_mul] using integrable_shift (line_lipschitz hf x c) 0 1

lemma integrable_exp_ambient {L : ℝ≥0} {f : E → ℝ} (hf : LipschitzWith L f) (a : ℝ) (x c : E) :
    Integrable (fun z : ℝ => Real.exp (a*f (x+z • c))) (gaussianReal 0 1) := by
  simpa only [zero_add, one_mul] using integrable_exp_shift (line_lipschitz hf x c) a 0 1

lemma ambientMass_pos {L : ℝ≥0} {f : E → ℝ} (hf : LipschitzWith L f) (a : ℝ) (c x : E) :
    0 < ambientMass a c f x := integral_exp_pos (integrable_exp_ambient hf a x c)

lemma integrable_ambient_weight {L : ℝ≥0} {f g : E → ℝ} (hf : LipschitzWith L f)
    (hg : Continuous g) {M : ℝ} (hM : ∀ x, |g x| ≤ M) (a : ℝ) (c x : E) :
    Integrable (fun z => Real.exp (a*f (x+z • c))*g (x+z • c)) (gaussianReal 0 1) := by
  apply (integrable_exp_ambient hf a x c).mul_bdd (by fun_prop)
  exact ae_of_all _ fun z => by simpa only [Real.norm_eq_abs] using hM (x+z • c)

lemma ambientStep_lipschitz {L : ℝ≥0} {f : E → ℝ} (hf : LipschitzWith L f)
    {a : ℝ} (ha : 0 ≤ a) (c : E) : LipschitzWith L (ambientStep a c f) := by
  rw [lipschitzWith_iff_norm_sub_le]
  intro x y
  rw [Real.norm_eq_abs]
  apply logMean_stable ha (integrable_ambient hf x c) (integrable_ambient hf y c)
    (integrable_exp_ambient hf a x c) (integrable_exp_ambient hf a y c)
  intro z
  simpa only [Real.norm_eq_abs, add_sub_add_right_eq_sub] using
    hf.norm_sub_le (x+z • c) (y+z • c)

lemma ambient_exp_near_le {L : ℝ≥0} {f : E → ℝ} (hf : LipschitzWith L f)
    (a : ℝ) (x₀ c : E) {x : E} (hx : ‖x-x₀‖ ≤ 1) (z : ℝ) :
    Real.exp (a*f (x+z • c)) ≤
      Real.exp (|a| *(|f x₀|+L))*Real.exp ((|a| *L*‖c‖)*|z|) := by
  have hb : |f (x+z • c)| ≤ |f x₀| + L + (L:ℝ)*‖c‖*|z| := by
    have hv := hf.norm_sub_le (x+z • c) x₀
    have ht := norm_add_le (x-x₀) (z • c)
    have he : x+z • c-x₀ = (x-x₀)+z • c := by abel
    rw [he] at hv
    rw [norm_smul, Real.norm_eq_abs] at ht
    have htri := abs_add_le (f (x+z • c)-f x₀) (f x₀)
    rw [sub_add_cancel] at htri
    rw [Real.norm_eq_abs] at hv
    nlinarith [L.coe_nonneg]
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  calc
    _ ≤ |a| * |f (x+z • c)| := by simpa only [abs_mul] using le_abs_self (a*f (x+z • c))
    _ ≤ |a| *(|f x₀|+L+(L:ℝ)*‖c‖*|z|) := mul_le_mul_of_nonneg_left hb (abs_nonneg _)
    _ = _ := by ring

lemma continuous_ambientMoment {L : ℝ≥0} {f g : E → ℝ} (hf : LipschitzWith L f)
    (hg : Continuous g) {M : ℝ} (hM : ∀ x, |g x| ≤ M) (a : ℝ) (c : E) :
    Continuous (ambientMoment a c f g) := by
  have hc := hf.continuous
  apply continuous_iff_continuousAt.mpr
  intro x₀
  apply continuousAt_of_dominated
    (bound := fun z => (Real.exp (|a| *(|f x₀|+L))*Real.exp ((|a| *L*‖c‖)*|z|))*M)
  · exact Eventually.of_forall fun _ => (integrable_ambient_weight hf hg hM a c _).aestronglyMeasurable
  · filter_upwards [Metric.ball_mem_nhds x₀ (by norm_num : (0:ℝ)<1)] with x hx
    exact ae_of_all _ fun z => by
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
      apply mul_le_mul (ambient_exp_near_le hf a x₀ c (by have hh : dist x x₀ < 1 := hx; simpa only [dist_eq_norm] using hh.le) z)
        (hM _) (abs_nonneg _)
      positivity
  · exact ((integrable_exp_abs _).const_mul _).mul_const _
  · exact ae_of_all _ fun z => by fun_prop

lemma continuous_ambientTilt {L : ℝ≥0} {f g : E → ℝ} (hf : LipschitzWith L f)
    (hg : Continuous g) {M : ℝ} (hM : ∀ x, |g x| ≤ M) (a : ℝ) (c : E) :
    Continuous (ambientTilt a c f g) := by
  have he : ambientMass a c f = ambientMoment a c f (fun _ => 1) := by
    funext x
    simp [ambientMass, ambientMoment]
  have hm : Continuous (ambientMass a c f) := by
    rw [he]
    exact continuous_ambientMoment hf continuous_const (by intro; norm_num : ∀ x : E, |(1:ℝ)| ≤ 1) a c
  exact (continuous_ambientMoment hf hg hM a c).div hm (fun x => (ambientMass_pos hf a c x).ne')

@[simp] lemma ambientTilt_zero (c : E) (f g : E → ℝ) (x : E) :
    ambientTilt 0 c f g x = ∫ z, g (x+z • c) ∂gaussianReal 0 1 := by
  simp [ambientTilt, ambientMoment, ambientMass]

lemma abs_ambientTilt_le {L : ℝ≥0} {f g : E → ℝ} (hf : LipschitzWith L f)
    (hg : Continuous g) {M : ℝ} (hM : ∀ x, |g x| ≤ M) (a : ℝ) (c x : E) :
    |ambientTilt a c f g x| ≤ M := by
  have hi := integrable_ambient_weight hf hg hM a c x
  have hp := ambientMass_pos hf a c x
  unfold ambientTilt
  rw [abs_div, abs_of_pos hp, div_le_iff₀ hp]
  apply abs_integral_le_integral_abs.trans
  have h := integral_mono hi.abs ((integrable_exp_ambient hf a x c).const_mul M)
    (fun z => by
      rw [abs_mul, abs_of_pos (Real.exp_pos _), mul_comm M]
      exact mul_le_mul_of_nonneg_left (hM _) (Real.exp_pos _).le)
  simpa only [integral_const_mul, ambientMass] using h

end Ambient
end ParisiFinite

 

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology
namespace ParisiFinite
section Ambient
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma ambient_exp_near_le_radius {L : ℝ≥0} {f : E → ℝ} (hf : LipschitzWith L f)
    (a : ℝ) (x₀ c : E) {x : E} {r : ℝ} (hx : ‖x-x₀‖ ≤ r) (z : ℝ) :
    Real.exp (a*f (x+z • c)) ≤
      Real.exp (|a| * (|f x₀|+(L:ℝ)*r))*Real.exp ((|a| * L*‖c‖)*|z|) := by
  have hb : |f (x+z • c)| ≤ |f x₀| + (L:ℝ)*r + (L:ℝ)*‖c‖*|z| := by
    have hv := hf.norm_sub_le (x+z • c) x₀
    have ht := norm_add_le (x-x₀) (z • c)
    have he : x+z • c-x₀ = (x-x₀)+z • c := by abel
    rw [he] at hv
    rw [norm_smul, Real.norm_eq_abs] at ht
    have htri := abs_add_le (f (x+z • c)-f x₀) (f x₀)
    rw [sub_add_cancel] at htri
    rw [Real.norm_eq_abs] at hv
    nlinarith [L.coe_nonneg]
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  calc
    _ ≤ |a| * |f (x+z • c)| := by simpa only [abs_mul] using le_abs_self (a*f (x+z • c))
    _ ≤ |a| * (|f x₀|+(L:ℝ)*r+(L:ℝ)*‖c‖*|z|) := mul_le_mul_of_nonneg_left hb (abs_nonneg _)
    _ = _ := by ring

 

lemma hasDerivAt_ambientMoment {L : ℝ≥0} {f f' g g' : E → ℝ} (hf : LipschitzWith L f)
    (hf' : Continuous f') (hg : Continuous g) (hg' : Continuous g')
    {M N P : ℝ≥0} (hM : ∀ x, |f' x| ≤ M) (hN : ∀ x, |g x| ≤ N) (hP : ∀ x, |g' x| ≤ P)
    (v : E)
    (hdf : ∀ y t, HasDerivAt (fun u : ℝ => f (y+u • v)) (f' (y+t • v)) t)
    (hdg : ∀ y t, HasDerivAt (fun u : ℝ => g (y+u • v)) (g' (y+t • v)) t)
    (a : ℝ) (c x : E) (t₀ : ℝ) :
    HasDerivAt (fun t => ambientMoment a c f g (x+t • v))
      (∫ z, Real.exp (a*f (x+t₀ • v+z • c))*
        (a*f' (x+t₀ • v+z • c)*g (x+t₀ • v+z • c)+g' (x+t₀ • v+z • c)) ∂gaussianReal 0 1) t₀ := by
  have hc := hf.continuous
  apply (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (s := Metric.ball t₀ 1)
    (bound := fun z =>
      (Real.exp (|a| * (|f (x+t₀ • v)|+(L:ℝ)*‖v‖))*Real.exp ((|a| * L*‖c‖)*|z|)) * (|a| * M*N+P))
    (F' := fun t z => Real.exp (a*f (x+t • v+z • c))*
      (a*f' (x+t • v+z • c)*g (x+t • v+z • c)+g' (x+t • v+z • c)))
    (Metric.ball_mem_nhds _ (by norm_num)) ?_ ?_ ?_ ?_ ?_ ?_).2
  · exact Eventually.of_forall fun _ => by fun_prop
  · exact integrable_ambient_weight hf hg hN a c (x+t₀ • v)
  · fun_prop
  · exact ae_of_all _ fun z t ht => by
      have hxt : ‖(x+t • v)-(x+t₀ • v)‖ ≤ ‖v‖ := by
        rw [add_sub_add_left_eq_sub, ← sub_smul, norm_smul, Real.norm_eq_abs]
        apply mul_le_of_le_one_left (norm_nonneg _)
        have hh : dist t t₀ < 1 := ht
        simpa only [Real.dist_eq] using hh.le
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
      apply mul_le_mul (ambient_exp_near_le_radius hf a (x+t₀ • v) c hxt z)
      · apply (abs_add_le _ _).trans
        rw [abs_mul, abs_mul]
        exact add_le_add (mul_le_mul
          (mul_le_mul_of_nonneg_left (hM _) (abs_nonneg a)) (hN _)
          (abs_nonneg _) (by positivity)) (hP _)
      · exact abs_nonneg _
      · positivity
  · exact ((integrable_exp_abs _).const_mul _).mul_const _
  · exact ae_of_all _ fun z t _ => by
      have he (u : ℝ) : x+u • v+z • c = (x+z • c)+u • v := by abel
      simp_rw [he]
      convert ((hdf (x+z • c) t).const_mul a).exp.mul (hdg (x+z • c) t) using 1
      first | rfl | ring

lemma hasDerivAt_ambientMass {L : ℝ≥0} {f f' : E → ℝ} (hf : LipschitzWith L f)
    (hf' : Continuous f') {M : ℝ≥0} (hM : ∀ x, |f' x| ≤ M) (v : E)
    (hdf : ∀ y t, HasDerivAt (fun u : ℝ => f (y+u • v)) (f' (y+t • v)) t)
    (a : ℝ) (c x : E) (t₀ : ℝ) :
    HasDerivAt (fun t => ambientMass a c f (x+t • v))
      (a*ambientMoment a c f f' (x+t₀ • v)) t₀ := by
  have h := hasDerivAt_ambientMoment hf hf' continuous_const continuous_const hM
    (N := 1) (P := 0) (by intro; norm_num) (by intro; norm_num) v hdf
    (fun y t => hasDerivAt_const t (1:ℝ)) a c x t₀
  have he : ambientMoment a c f (fun _ => 1) = ambientMass a c f := by
    funext y
    simp [ambientMoment, ambientMass]
  rw [he] at h
  simpa only [mul_one, add_zero, mul_left_comm _ a, integral_const_mul, ambientMoment] using h

lemma hasDerivAt_ambientMean {L : ℝ≥0} {f f' : E → ℝ} (hf : LipschitzWith L f)
    (hf' : Continuous f') {M : ℝ≥0} (hM : ∀ x, |f' x| ≤ M) (v : E)
    (hdf : ∀ y t, HasDerivAt (fun u : ℝ => f (y+u • v)) (f' (y+t • v)) t)
    (c x : E) (t₀ : ℝ) :
    HasDerivAt (fun t => ∫ z, f (x+t • v+z • c) ∂gaussianReal 0 1)
      (∫ z, f' (x+t₀ • v+z • c) ∂gaussianReal 0 1) t₀ := by
  have hc := hf.continuous
  apply (hasDerivAt_integral_of_dominated_loc_of_deriv_le (s := Set.univ)
    (bound := fun _ => (M:ℝ)) (F' := fun t z => f' (x+t • v+z • c)) univ_mem ?_
    (integrable_ambient hf (x+t₀ • v) c) (by fun_prop) ?_ (integrable_const _) ?_).2
  · exact Eventually.of_forall fun _ => by fun_prop
  · exact ae_of_all _ fun z t _ => by simpa only [Real.norm_eq_abs] using hM _
  · exact ae_of_all _ fun z t _ => by
      have he (u : ℝ) : x+u • v+z • c = (x+z • c)+u • v := by abel
      simpa only [he] using hdf (x+z • c) t

lemma hasDerivAt_ambientStep {L : ℝ≥0} {f f' : E → ℝ} (hf : LipschitzWith L f)
    (hf' : Continuous f') {M : ℝ≥0} (hM : ∀ x, |f' x| ≤ M) (v : E)
    (hdf : ∀ y t, HasDerivAt (fun u : ℝ => f (y+u • v)) (f' (y+t • v)) t)
    (a : ℝ) (c x : E) (t₀ : ℝ) :
    HasDerivAt (fun t => ambientStep a c f (x+t • v))
      (ambientTilt a c f f' (x+t₀ • v)) t₀ := by
  by_cases ha : a=0
  · subst a
    simpa only [ambientStep, logMean_zero, ambientTilt_zero] using
      hasDerivAt_ambientMean hf hf' hM v hdf c x t₀
  · have h := ((hasDerivAt_ambientMass hf hf' hM v hdf a c x t₀).log
      (ambientMass_pos hf a c (x+t₀ • v)).ne').div_const a
    have he : (a*ambientMoment a c f f' (x+t₀ • v)/ambientMass a c f (x+t₀ • v))/a =
        ambientTilt a c f f' (x+t₀ • v) := by
      unfold ambientTilt
      field_simp
    rw [he] at h
    have heq : (fun t : ℝ => ambientStep a c f (x+t • v)) =
        (fun t : ℝ => Real.log (ambientMass a c f (x+t • v))/a) := by
      funext t
      simp [ambientStep, logMean, ha, ambientMass]
    rw [heq]
    exact h

end Ambient
end ParisiFinite

 

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology
namespace ParisiFinite
section Ambient
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma ambientMoment_add {L : ℝ≥0} {f g h : E → ℝ} (hf : LipschitzWith L f)
    (hg : Continuous g) (hh : Continuous h) {M N : ℝ}
    (hM : ∀ x, |g x| ≤ M) (hN : ∀ x, |h x| ≤ N) (a : ℝ) (c x : E) :
    ambientMoment a c f (fun y => g y+h y) x =
      ambientMoment a c f g x + ambientMoment a c f h x := by
  simp only [ambientMoment, mul_add]
  exact integral_add (integrable_ambient_weight hf hg hM a c x) (integrable_ambient_weight hf hh hN a c x)

lemma ambientMoment_const_mul (a : ℝ) (c : E) (f g : E → ℝ) (x : E) (k : ℝ) :
    ambientMoment a c f (fun y => k*g y) x = k*ambientMoment a c f g x := by
  simp only [ambientMoment, mul_left_comm _ k, integral_const_mul]

lemma ambientTilt_add {L : ℝ≥0} {f g h : E → ℝ} (hf : LipschitzWith L f)
    (hg : Continuous g) (hh : Continuous h) {M N : ℝ}
    (hM : ∀ x, |g x| ≤ M) (hN : ∀ x, |h x| ≤ N) (a : ℝ) (c x : E) :
    ambientTilt a c f (fun y => g y+h y) x =
      ambientTilt a c f g x + ambientTilt a c f h x := by
  simp only [ambientTilt, ambientMoment_add hf hg hh hM hN, add_div]

lemma ambientTilt_const_mul (a : ℝ) (c : E) (f g : E → ℝ) (x : E) (k : ℝ) :
    ambientTilt a c f (fun y => k*g y) x = k*ambientTilt a c f g x := by
  simp only [ambientTilt, ambientMoment_const_mul, mul_div_assoc]

lemma ambientTilt_mono {L : ℝ≥0} {f g h : E → ℝ} (hf : LipschitzWith L f)
    (hg : Continuous g) (hh : Continuous h) {M N : ℝ}
    (hM : ∀ x, |g x| ≤ M) (hN : ∀ x, |h x| ≤ N)
    (hgh : ∀ x, g x ≤ h x) (a : ℝ) (c x : E) :
    ambientTilt a c f g x ≤ ambientTilt a c f h x := by
  apply div_le_div_of_nonneg_right _ (ambientMass_pos hf a c x).le
  apply integral_mono (integrable_ambient_weight hf hg hM a c x)
    (integrable_ambient_weight hf hh hN a c x)
  intro z
  exact mul_le_mul_of_nonneg_left (hgh _) (Real.exp_pos _).le

lemma ambientTilt_const {L : ℝ≥0} {f : E → ℝ} (hf : LipschitzWith L f)
    (a : ℝ) (c x : E) (k : ℝ) :
    ambientTilt a c f (fun _ => k) x = k := by
  simp only [ambientTilt, ambientMoment, integral_mul_const, ambientMass]
  exact mul_div_cancel_left₀ _ (ambientMass_pos hf a c x).ne'

 
lemma hasDerivAt_ambientTilt {L : ℝ≥0} {f f' g g' : E → ℝ} (hf : LipschitzWith L f)
    (hf' : Continuous f') (hg : Continuous g) (hg' : Continuous g')
    {M N P : ℝ≥0} (hM : ∀ x, |f' x| ≤ M) (hN : ∀ x, |g x| ≤ N) (hP : ∀ x, |g' x| ≤ P)
    (v : E)
    (hdf : ∀ y t, HasDerivAt (fun u : ℝ => f (y+u • v)) (f' (y+t • v)) t)
    (hdg : ∀ y t, HasDerivAt (fun u : ℝ => g (y+u • v)) (g' (y+t • v)) t)
    (a : ℝ) (c x : E) (t₀ : ℝ) :
    HasDerivAt (fun t => ambientTilt a c f g (x+t • v))
      (ambientTilt a c f g' (x+t₀ • v) + a*
        (ambientTilt a c f (fun y => f' y*g y) (x+t₀ • v) -
          ambientTilt a c f f' (x+t₀ • v)*ambientTilt a c f g (x+t₀ • v))) t₀ := by
  have h := hasDerivAt_ambientMoment hf hf' hg hg' hM hN hP v hdf hdg a c x t₀
  have he (y : E) : a*f' y*g y+g' y = g' y+a*(f' y*g y) := by ring
  simp_rw [he] at h
  change HasDerivAt (fun t => ambientMoment a c f g (x+t • v))
    (ambientMoment a c f (fun y => g' y+a*(f' y*g y)) (x+t₀ • v)) t₀ at h
  rw [ambientMoment_add hf hg' (by fun_prop) hP
    (fun y => by
      rw [abs_mul, abs_mul]
      exact mul_le_mul_of_nonneg_left (mul_le_mul (hM _) (hN _) (abs_nonneg _) M.coe_nonneg) (abs_nonneg a)),
    ambientMoment_const_mul] at h
  have hd := h.div (hasDerivAt_ambientMass hf hf' hM v hdf a c x t₀)
    (ambientMass_pos hf a c (x+t₀ • v)).ne'
  convert hd using 1 <;> first | rfl | (unfold ambientTilt; field_simp; ring)

end Ambient
end ParisiFinite

 

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology
namespace ParisiFinite

 

structure DirectionalField (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] where
  val : E → ℝ
  first : E → E → ℝ
  second : E → E → E → ℝ
  lip : ℝ≥0
  lipschitz : LipschitzWith lip val
  continuousFirst : ∀ v, Continuous (first v)
  continuousSecond : ∀ v w, Continuous (second v w)
  hasFirst : ∀ v x t, HasDerivAt (fun u : ℝ => val (x+u • v)) (first v (x+t • v)) t
  hasSecond : ∀ v w x t, HasDerivAt (fun u : ℝ => first w (x+u • v)) (second v w (x+t • v)) t
  boundFirst : E → ℝ≥0
  boundSecond : E → E → ℝ≥0
  normFirst : ∀ v x, |first v x| ≤ boundFirst v
  normSecond : ∀ v w x, |second v w x| ≤ boundSecond v w

namespace DirectionalField
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

 

def transform (f : DirectionalField E) (a : ℝ≥0) (c : E) : DirectionalField E where
  val := ambientStep a c f.val
  first v := ambientTilt a c f.val (f.first v)
  second v w x := ambientTilt a c f.val (f.second v w) x + (a:ℝ)*
    (ambientTilt a c f.val (fun y => f.first v y*f.first w y) x -
      ambientTilt a c f.val (f.first v) x*ambientTilt a c f.val (f.first w) x)
  lip := f.lip
  lipschitz := ambientStep_lipschitz f.lipschitz a.coe_nonneg c
  continuousFirst v := continuous_ambientTilt f.lipschitz (f.continuousFirst v) (f.normFirst v) a c
  continuousSecond v w := by
    have h1 := continuous_ambientTilt f.lipschitz (f.continuousFirst v) (f.normFirst v) a c
    have h2 := continuous_ambientTilt f.lipschitz (f.continuousFirst w) (f.normFirst w) a c
    have h12 := continuous_ambientTilt f.lipschitz (f.continuousSecond v w) (f.normSecond v w) a c
    have hp := continuous_ambientTilt f.lipschitz ((f.continuousFirst v).mul (f.continuousFirst w))
      (fun y => by
        simp only [Pi.mul_apply, abs_mul]
        exact mul_le_mul (f.normFirst v y) (f.normFirst w y) (abs_nonneg _) (f.boundFirst v).coe_nonneg) (a:ℝ) c
    fun_prop
  hasFirst v x t := hasDerivAt_ambientStep f.lipschitz (f.continuousFirst v) (f.normFirst v)
    v (f.hasFirst v) a c x t
  hasSecond v w x t := hasDerivAt_ambientTilt f.lipschitz (f.continuousFirst v)
    (f.continuousFirst w) (f.continuousSecond v w) (f.normFirst v) (f.normFirst w)
    (f.normSecond v w) v (f.hasFirst v) (f.hasSecond v w) a c x t
  boundFirst := f.boundFirst
  boundSecond v w := f.boundSecond v w + 2*a*f.boundFirst v*f.boundFirst w
  normFirst v := abs_ambientTilt_le f.lipschitz (f.continuousFirst v) (f.normFirst v) a c
  normSecond v w x := by
    have h1 := abs_ambientTilt_le f.lipschitz (f.continuousFirst v) (f.normFirst v) (a:ℝ) c x
    have h2 := abs_ambientTilt_le f.lipschitz (f.continuousFirst w) (f.normFirst w) (a:ℝ) c x
    have h12 := abs_ambientTilt_le f.lipschitz (f.continuousSecond v w) (f.normSecond v w) (a:ℝ) c x
    have hp := abs_ambientTilt_le f.lipschitz ((f.continuousFirst v).mul (f.continuousFirst w))
      (fun y => by
        simp only [Pi.mul_apply, abs_mul]
        exact mul_le_mul (f.normFirst v y) (f.normFirst w y) (abs_nonneg _) (f.boundFirst v).coe_nonneg) (a:ℝ) c x
    change |ambientTilt a c f.val (fun y => f.first v y * f.first w y) x| ≤
      (f.boundFirst v : ℝ) * (f.boundFirst w : ℝ) at hp
    have hprod := mul_le_mul h1 h2 (abs_nonneg _) (f.boundFirst v).coe_nonneg
    have hsub := abs_sub_le (ambientTilt a c f.val (fun y => f.first v y*f.first w y) x) 0
      (ambientTilt a c f.val (f.first v) x*ambientTilt a c f.val (f.first w) x)
    simp only [sub_zero, zero_sub, abs_neg, abs_mul] at hsub
    apply (abs_add_le _ _).trans
    rw [abs_mul, abs_of_nonneg a.coe_nonneg]
    simp only [NNReal.coe_add, NNReal.coe_mul, NNReal.coe_ofNat]
    nlinarith [a.coe_nonneg]

 
def slice (f : DirectionalField E) (x v : E) : SmoothField where
  val t := f.val (x+t • v)
  d1 t := f.first v (x+t • v)
  d2 t := f.second v v (x+t • v)
  hasD1 := f.hasFirst v x
  hasD2 := f.hasSecond v v x
  continuousD2 := (f.continuousSecond v v).comp (by fun_prop)
  bound1 := f.boundFirst v
  bound2 := f.boundSecond v v
  normD1 t := f.normFirst v _
  normD2 t := f.normSecond v v _

 
lemma hasDerivAt_transform_scale (f : DirectionalField E) (a : ℝ≥0) (c x : E) (s : ℝ) :
    HasDerivAt (fun r => (f.transform a (r • c)).val x)
      (s*(ambientTilt a (s • c) f.val (f.second c c) x +
        (a:ℝ)*ambientTilt a (s • c) f.val (fun y => (f.first c y)^2) x)) s := by
  have h := ParisiFinite.hasDerivAt_step_scale (f.slice x c) a s 0
  convert h using 1 <;>
    simp only [transform, slice, step, ambientStep, ambientTilt, tiltedMean, expMoment,
      expMass, ambientMass, ambientMoment, zero_add, smul_smul, mul_comm]

end DirectionalField
end ParisiFinite

end

end OAI
