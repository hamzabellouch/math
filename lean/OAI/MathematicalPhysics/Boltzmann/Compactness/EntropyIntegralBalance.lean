import OAI.MathematicalPhysics.Boltzmann.Admissibility
import OAI.MathematicalPhysics.Boltzmann.Approximation.RegularizedLogBounds
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.Topology.Order.Lattice

namespace OAI

section

/-! # The regularized entropy primitive used at zeros of finite approximations -/

noncomputable section

open Filter
open scoped Topology

namespace BoltzmannNonuniqueness

def scalarRelativeEntropy (m f : ℝ) : ℝ := f*Real.log f-f*(1+Real.log m)+m

theorem scalarRelativeEntropy_eq {m : ℝ} (hm : 0 < m) (f : ℝ) :
    scalarRelativeEntropy m f = f*Real.log (f/m)-f+m := by
  by_cases hf : f = 0
  · simp [scalarRelativeEntropy,hf]
  · rw [Real.log_div hf hm.ne']
    unfold scalarRelativeEntropy
    ring

theorem scalarRelativeEntropy_continuous (m : ℝ) : Continuous (scalarRelativeEntropy m) :=
  (Real.continuous_mul_log.sub (continuous_id.mul_const (1+Real.log m))).add_const m

theorem scalarRelativeEntropy_hasDerivAt {m f : ℝ} (hm : 0 < m) (hf : 0 < f) :
    HasDerivAt (scalarRelativeEntropy m) (Real.log (f/m)) f := by
  have h := ((Real.hasDerivAt_mul_log hf.ne').sub
    ((hasDerivAt_id f).mul_const (1+Real.log m))).add_const m
  rw [Real.log_div hf.ne' hm.ne']
  convert h using 1
  · funext x
    rfl
  · ring

def regularizedEntropy (m e δ f : ℝ) : ℝ :=
  scalarRelativeEntropy m (f+δ*e)-scalarRelativeEntropy m (δ*e)+m

theorem regularizedEntropy_continuous_delta (m e f : ℝ) :
    Continuous (fun δ => regularizedEntropy m e δ f) :=
  (((scalarRelativeEntropy_continuous m).comp
    (continuous_const.add (continuous_id.mul_const e))).sub
    ((scalarRelativeEntropy_continuous m).comp (continuous_id.mul_const e))).add_const m

theorem regularizedEntropy_tendsto (m e f : ℝ) :
    Tendsto (fun δ => regularizedEntropy m e δ f) (𝓝 0) (𝓝 (scalarRelativeEntropy m f)) := by
  have h := (regularizedEntropy_continuous_delta m e f).tendsto 0
  have he : regularizedEntropy m e 0 f = scalarRelativeEntropy m f := by
    simp [regularizedEntropy,scalarRelativeEntropy]
  rw [he] at h
  exact h

theorem regularizedEntropy_hasDerivAt {m e δ f : ℝ}
    (hm : 0 < m) (he : 0 < e) (hδ : 0 < δ) (hf : 0 ≤ f) :
    HasDerivAt (regularizedEntropy m e δ) (Real.log ((f+δ*e)/m)) f := by
  have hp : 0 < f+δ*e := add_pos_of_nonneg_of_pos hf (mul_pos hδ he)
  have h := (((scalarRelativeEntropy_hasDerivAt hm hp).comp f
    ((hasDerivAt_id f).add_const (δ*e))).sub_const (scalarRelativeEntropy m (δ*e))).add_const m
  convert h using 1
  · funext x
    rfl
  · ring

end BoltzmannNonuniqueness

end

end

section

/-!
# Lower semicontinuity of entropy production

The extended scalar entropy production is lower semicontinuous along positive
approximations of nonnegative products. In particular its value is infinite
when exactly one limiting product vanishes. Weighted Fatou then passes this
production to a limit, without a domination hypothesis or a finite-production
assumption. The final specialization applies to positive regularizations of
four nonnegative factors.
-/

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal Topology

namespace BoltzmannNonuniqueness

theorem extendedEntropyProduction_symm (a b : ℝ) :
    extendedEntropyProduction a b = extendedEntropyProduction b a := by
  by_cases hz : a = 0 ∧ b = 0
  · simp [extendedEntropyProduction, hz.1, hz.2]
  have hz' : ¬ (b = 0 ∧ a = 0) := fun h => hz ⟨h.2, h.1⟩
  by_cases hp : 0 < a ∧ 0 < b
  · have hp' : 0 < b ∧ 0 < a := ⟨hp.2, hp.1⟩
    simp only [extendedEntropyProduction, ite_eq_right hz, ite_eq_right hz',
      ite_eq_left hp, ite_eq_left hp']
    congr 1
    rw [Real.log_div hp.1.ne' hp.2.ne', Real.log_div hp.2.ne' hp.1.ne']
    ring
  · have hp' : ¬ (0 < b ∧ 0 < a) := fun h => hp ⟨h.2, h.1⟩
    simp only [extendedEntropyProduction, ite_eq_right hz, ite_eq_right hz',
      ite_eq_right hp, ite_eq_right hp']

theorem measurable_extendedEntropyProduction {X : Type*} [MeasurableSpace X]
    {a b : X → ℝ} (ha : Measurable a) (hb : Measurable b) :
    Measurable (fun x => extendedEntropyProduction (a x) (b x)) := by
  unfold extendedEntropyProduction
  apply Measurable.ite
    ((measurableSet_eq_fun ha measurable_const).inter
      (measurableSet_eq_fun hb measurable_const)) measurable_const
  exact Measurable.ite
    ((measurableSet_lt measurable_const ha).inter (measurableSet_lt measurable_const hb))
    ((ha.sub hb).mul ((ha.div hb).log)).ennreal_ofReal measurable_const

private theorem production_eventually_eq {ι : Type*} {l : Filter ι}
    {a b : ι → ℝ} (ha : ∀ᶠ i in l, 0 < a i) (hb : ∀ᶠ i in l, 0 < b i) :
    (fun i => extendedEntropyProduction (a i) (b i)) =ᶠ[l]
      (fun i => ENNReal.ofReal ((a i - b i) * Real.log (a i / b i))) := by
  filter_upwards [ha, hb] with i hai hbi
  simp [extendedEntropyProduction, hai, hbi, hai.ne', hbi.ne']

theorem tendsto_extendedEntropyProduction_positive {ι : Type*} {l : Filter ι}
    {a b : ι → ℝ} {A B : ℝ}
    (ha : Tendsto a l (𝓝 A)) (hb : Tendsto b l (𝓝 B))
    (hA : 0 < A) (hB : 0 < B)
    (hap : ∀ᶠ i in l, 0 < a i) (hbp : ∀ᶠ i in l, 0 < b i) :
    Tendsto (fun i => extendedEntropyProduction (a i) (b i)) l
      (𝓝 (extendedEntropyProduction A B)) := by
  have ht := ENNReal.tendsto_ofReal ((ha.sub hb).mul
    ((ha.div hb hB.ne').log (div_pos hA hB).ne'))
  have he : extendedEntropyProduction A B =
      ENNReal.ofReal ((A - B) * Real.log (A / B)) := by
    simp [extendedEntropyProduction, hA, hB, hA.ne', hB.ne']
  rw [he]
  exact ht.congr' (production_eventually_eq hap hbp).symm

/-- A zero product against a positive product has infinite limiting production. -/
theorem tendsto_extendedEntropyProduction_zero_left {ι : Type*} {l : Filter ι}
    {a b : ι → ℝ} {B : ℝ}
    (ha : Tendsto a l (𝓝 0)) (hb : Tendsto b l (𝓝 B)) (hB : 0 < B)
    (hap : ∀ᶠ i in l, 0 < a i) (hbp : ∀ᶠ i in l, 0 < b i) :
    Tendsto (fun i => extendedEntropyProduction (a i) (b i)) l (𝓝 ∞) := by
  have hr : Tendsto (fun i => a i / b i) l (𝓝[>] (0 : ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · simpa only [zero_div, Pi.div_def] using ha.div hb hB.ne'
    · filter_upwards [hap, hbp] with i hai hbi
      exact div_pos hai hbi
  have hlog := Real.tendsto_log_nhdsGT_zero.comp hr
  have hdiff : Tendsto (fun i => a i - b i) l (𝓝 (-B)) := by
    simpa only [zero_sub] using ha.sub hb
  have hprod := hdiff.neg_mul_atBot (neg_lt_zero.mpr hB) hlog
  have ht := ENNReal.tendsto_ofReal_atTop.comp hprod
  exact ht.congr' (production_eventually_eq hap hbp).symm

theorem tendsto_extendedEntropyProduction_zero_right {ι : Type*} {l : Filter ι}
    {a b : ι → ℝ} {A : ℝ}
    (ha : Tendsto a l (𝓝 A)) (hb : Tendsto b l (𝓝 0)) (hA : 0 < A)
    (hap : ∀ᶠ i in l, 0 < a i) (hbp : ∀ᶠ i in l, 0 < b i) :
    Tendsto (fun i => extendedEntropyProduction (a i) (b i)) l (𝓝 ∞) := by
  simpa only [extendedEntropyProduction_symm] using
    tendsto_extendedEntropyProduction_zero_left hb ha hA hbp hap

theorem extendedEntropyProduction_le_liminf {ι : Type*} {l : Filter ι} [NeBot l]
    {a b : ι → ℝ} {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (ha : Tendsto a l (𝓝 A)) (hb : Tendsto b l (𝓝 B))
    (hap : ∀ᶠ i in l, 0 < a i) (hbp : ∀ᶠ i in l, 0 < b i) :
    extendedEntropyProduction A B ≤
      liminf (fun i => extendedEntropyProduction (a i) (b i)) l := by
  by_cases hAz : A = 0
  · subst A
    by_cases hBz : B = 0
    · simp only [hBz, extendedEntropyProduction, and_self, ite_true]
      exact bot_le
    · have hBp : 0 < B := lt_of_le_of_ne hB (Ne.symm hBz)
      rw [(tendsto_extendedEntropyProduction_zero_left ha hb hBp hap hbp).liminf_eq]
      exact le_top
  · have hAp : 0 < A := lt_of_le_of_ne hA (Ne.symm hAz)
    by_cases hBz : B = 0
    · subst B
      rw [(tendsto_extendedEntropyProduction_zero_right ha hb hAp hap hbp).liminf_eq]
      exact le_top
    · have hBp : 0 < B := lt_of_le_of_ne hB (Ne.symm hBz)
      rw [(tendsto_extendedEntropyProduction_positive ha hb hAp hBp hap hbp).liminf_eq]

/-- Weighted Fatou for the actual extended production, including infinite values. -/
theorem lintegral_extendedEntropyProduction_le_liminf
    {X ι : Type*} [MeasurableSpace X] {μ : Measure X} {l : Filter ι}
    [NeBot l] [IsCountablyGenerated l]
    {a b : ι → X → ℝ} {A B : X → ℝ} {w : X → ℝ≥0∞}
    (ha : ∀ i, Measurable (a i)) (hb : ∀ i, Measurable (b i)) (hw : Measurable w)
    (hA : ∀ᵐ x ∂μ, 0 ≤ A x) (hB : ∀ᵐ x ∂μ, 0 ≤ B x)
    (hconv : ∀ᵐ x ∂μ, Tendsto (fun i => a i x) l (𝓝 (A x)) ∧
      Tendsto (fun i => b i x) l (𝓝 (B x)))
    (hpos : ∀ᵐ x ∂μ, (∀ᶠ i in l, 0 < a i x) ∧ (∀ᶠ i in l, 0 < b i x)) :
    (∫⁻ x, w x * extendedEntropyProduction (A x) (B x) ∂μ) ≤
      liminf (fun i => ∫⁻ x, w x * extendedEntropyProduction (a i x) (b i x) ∂μ) l := by
  calc
    _ ≤ ∫⁻ x, liminf (fun i => w x * extendedEntropyProduction (a i x) (b i x)) l ∂μ := by
      apply lintegral_mono_ae
      filter_upwards [hA, hB, hconv, hpos] with x hAx hBx hx hpx
      have hs := extendedEntropyProduction_le_liminf hAx hBx hx.1 hx.2 hpx.1 hpx.2
      have hm := ENNReal.le_liminf_mul
        (u := fun _ : ι => w x) (v := fun i => extendedEntropyProduction (a i x) (b i x))
        (f := l)
      exact (mul_le_mul_right hs (w x)).trans (by simpa only [liminf_const, Pi.mul_def] using hm)
    _ ≤ _ := lintegral_liminf_le (fun i => hw.mul (measurable_extendedEntropyProduction (ha i) (hb i)))

/-- Positive perturbations of four nonnegative factors provide admissible approximations. -/
theorem extendedEntropyProduction_regularized_le_liminf
    {a b c d ga gb gc gd : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (hga : 0 < ga) (hgb : 0 < gb) (hgc : 0 < gc) (hgd : 0 < gd) :
    extendedEntropyProduction (a * b) (c * d) ≤
      liminf (fun δ : ℝ => extendedEntropyProduction
        ((a + δ * ga) * (b + δ * gb)) ((c + δ * gc) * (d + δ * gd))) (𝓝[>] 0) := by
  apply extendedEntropyProduction_le_liminf (mul_nonneg ha hb) (mul_nonneg hc hd)
  · simpa only [zero_mul, add_zero, id_eq] using
      (((tendsto_const_nhds.add (tendsto_id.mul_const ga)).mul
        (tendsto_const_nhds.add (tendsto_id.mul_const gb))).mono_left
        (show 𝓝[>] (0 : ℝ) ≤ 𝓝 0 from nhdsWithin_le_nhds))
  · simpa only [zero_mul, add_zero, id_eq] using
      (((tendsto_const_nhds.add (tendsto_id.mul_const gc)).mul
        (tendsto_const_nhds.add (tendsto_id.mul_const gd))).mono_left
        (show 𝓝[>] (0 : ℝ) ≤ 𝓝 0 from nhdsWithin_le_nhds))
  · filter_upwards [self_mem_nhdsWithin] with δ hδ
    exact mul_pos (add_pos_of_nonneg_of_pos ha (mul_pos hδ hga))
      (add_pos_of_nonneg_of_pos hb (mul_pos hδ hgb))
  · filter_upwards [self_mem_nhdsWithin] with δ hδ
    exact mul_pos (add_pos_of_nonneg_of_pos hc (mul_pos hδ hgc))
      (add_pos_of_nonneg_of_pos hd (mul_pos hδ hgd))

end BoltzmannNonuniqueness

end

end

section

/-! # A regularization-independent integrable bound for relative entropy -/

noncomputable section

open MeasureTheory
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness

theorem scalarRelativeEntropy_nonneg {m u : ℝ} (hm : 0 < m) (hu : 0 ≤ u) :
    0 ≤ scalarRelativeEntropy m u := by
  rw [scalarRelativeEntropy_eq hm]
  exact relativeEntropyDensity_nonneg hu hm

theorem scalarRelativeEntropy_le_power {m u p : ℝ} (hu : 0 ≤ u) (hp : 1 < p) :
    scalarRelativeEntropy m u ≤ u^p/(p-1)+|Real.log m| *u+m := by
  have hp' : 0 < p-1 := sub_pos.mpr hp
  have hpow : u*u^(p-1) = u^p := by
    by_cases hz : u = 0
    · simp [hz,Real.zero_rpow hp'.ne',Real.zero_rpow (by linarith : p ≠ 0)]
    · rw [mul_comm,← Real.rpow_add_one hz]
      congr 1
      ring
  have hlog := mul_le_mul_of_nonneg_left (Real.log_le_rpow_div hu hp') hu
  have he : u*(u^(p-1)/(p-1)) = u^p/(p-1) := by rw [← mul_div_assoc,hpow]
  rw [he] at hlog
  have hm := mul_le_mul_of_nonneg_right (neg_le_abs (Real.log m)) hu
  unfold scalarRelativeEntropy
  nlinarith

theorem abs_log_maxwellian_le (v : Velocity) :
    |Real.log (maxwellian v)| ≤ |-(3/2:ℝ)*Real.log (2*Real.pi)|+‖v‖^2/2 := by
  rw [log_maxwellian]
  exact (abs_sub (-(3/2:ℝ)*Real.log (2*Real.pi)) (‖v‖^2/2)).trans_eq
    (congrArg (fun x : ℝ => |-(3/2:ℝ)*Real.log (2*Real.pi)|+x)
      (abs_of_nonneg (show 0 ≤ ‖v‖^2/2 by positivity)))

def entropyPowerMajorant (q B p : ℝ) (v : Velocity) : ℝ :=
  (B^p/(p-1))*H q v^p+
    (|-(3/2:ℝ)*Real.log (2*Real.pi)|+‖v‖^2/2)*B*H q v+maxwellian v

theorem scalarRelativeEntropy_le_majorant {q B p u : ℝ} (hB : 0 ≤ B) (hp : 1 < p)
    (v : Velocity) (hu : 0 ≤ u) (hub : u ≤ B*H q v) :
    scalarRelativeEntropy (maxwellian v) u ≤ entropyPowerMajorant q B p v := by
  have hpow := Real.rpow_le_rpow hu hub (by linarith : 0 ≤ p)
  rw [Real.mul_rpow hB (H_nonneg q v)] at hpow
  have hquot := div_le_div_of_nonneg_right hpow (by linarith : 0 ≤ p-1)
  have hlog := mul_le_mul (abs_log_maxwellian_le v) hub hu (by positivity)
  have h := scalarRelativeEntropy_le_power (m := maxwellian v) hu hp
  unfold entropyPowerMajorant
  calc
    _ ≤ u^p/(p-1)+|Real.log (maxwellian v)| *u+maxwellian v := h
    _ ≤ (B^p*H q v^p)/(p-1)+
        (|-(3/2:ℝ)*Real.log (2*Real.pi)|+‖v‖^2/2)*(B*H q v)+maxwellian v := by
      linarith
    _ = _ := by ring

theorem entropyPowerMajorant_integrable {q B p : ℝ} (hq : q < 2)
    (hp : Integrable (fun v : Velocity => H q v^p)) :
    Integrable (entropyPowerMajorant q B p) := by
  have h := ((hp.const_mul (B^p/(p-1))).add
    (((integrable_H hq).const_mul (|-(3/2:ℝ)*Real.log (2*Real.pi)| *B)).add
      ((integrable_even_moment_H hq 1).const_mul (B/2)))).add integrable_maxwellian
  convert h using 1
  funext v
  simp only [entropyPowerMajorant,Nat.reduceMul,Pi.add_apply]
  ring

theorem bounded_relative_entropy_integrable {X : Type*} [MeasurableSpace X]
    {μ : Measure X} [IsFiniteMeasure μ] {q B p : ℝ} (hq : q < 2) (hB : 0 ≤ B)
    (hp : 1 < p) (hpi : Integrable (fun v : Velocity => H q v^p))
    {f : X × Velocity → ℝ} (hfm : Measurable f) (hfn : ∀ z, 0 ≤ f z)
    (hfb : ∀ z, f z ≤ B*H q z.2) :
    Integrable (fun z => scalarRelativeEntropy (maxwellian z.2) (f z)) (μ.prod volume) := by
  have hm : Measurable (fun z : X × Velocity => scalarRelativeEntropy (maxwellian z.2) (f z)) := by
    unfold scalarRelativeEntropy maxwellian
    fun_prop
  apply ((entropyPowerMajorant_integrable (B := B) hq hpi).comp_snd μ).mono' hm.aestronglyMeasurable
  filter_upwards [] with z
  rw [Real.norm_of_nonneg (scalarRelativeEntropy_nonneg (maxwellian_pos _) (hfn z))]
  exact scalarRelativeEntropy_le_majorant hB hp z.2 (hfn z) (hfb z)

end BoltzmannNonuniqueness

end

end

section

/-! # The regularized entropy chain rule on an absolutely continuous free path -/

noncomputable section

open MeasureTheory Set
open scoped NNReal

namespace BoltzmannNonuniqueness

theorem regularizedEntropy_lipschitz {m e δ R : ℝ}
    (hm : 0 < m) (he : 0 < e) (hδ : 0 < δ) (_hR : 0 ≤ R) :
    ∃ C : ℝ≥0, LipschitzOnWith C (regularizedEntropy m e δ) (Icc 0 R) := by
  let L := Real.log (δ*e/m)
  let U := Real.log ((R+δ*e)/m)
  let C : ℝ≥0 := ⟨|L|+|U|,add_nonneg (abs_nonneg _) (abs_nonneg _)⟩
  refine ⟨C,(convex_Icc (0:ℝ) R).lipschitzOnWith_of_nnnorm_hasDerivWithin_le
    (fun x hx => (regularizedEntropy_hasDerivAt hm he hδ hx.1).hasDerivWithinAt) ?_⟩
  intro x hx
  have hl : L ≤ Real.log ((x+δ*e)/m) := Real.log_le_log (div_pos (mul_pos hδ he) hm)
    (div_le_div_of_nonneg_right (by linarith [hx.1]) hm.le)
  have hu : Real.log ((x+δ*e)/m) ≤ U := Real.log_le_log
    (div_pos (add_pos_of_nonneg_of_pos hx.1 (mul_pos hδ he)) hm)
    (div_le_div_of_nonneg_right (by linarith [hx.2]) hm.le)
  have hb : |Real.log ((x+δ*e)/m)| ≤ |L|+|U| := abs_le.mpr ⟨by
    linarith [neg_abs_le L,abs_nonneg U],by linarith [le_abs_self U,abs_nonneg L]⟩
  exact_mod_cast hb

theorem regularizedEntropy_chain_rule {a b m e δ R : ℝ} {F r : ℝ → ℝ}
    (hm : 0 < m) (he : 0 < e) (hδ : 0 < δ) (hR : 0 ≤ R)
    (hF : AbsolutelyContinuousOnInterval F a b)
    (hFn : ∀ t ∈ uIcc a b, 0 ≤ F t) (hFb : ∀ t ∈ uIcc a b, F t ≤ R)
    (hr : ∀ᵐ t, t ∈ uIcc a b → HasDerivAt F (r t) t) :
    (∫ t in a..b, Real.log ((F t+δ*e)/m)*r t) =
      regularizedEntropy m e δ (F b)-regularizedEntropy m e δ (F a) := by
  obtain ⟨C,hC⟩ := regularizedEntropy_lipschitz hm he hδ hR
  have hc : AbsolutelyContinuousOnInterval (fun t => regularizedEntropy m e δ (F t)) a b :=
    hC.comp_absolutelyContinuousOnInterval (fun t ht => ⟨hFn t ht,hFb t ht⟩) hF
  rw [← hc.integral_deriv_eq_sub]
  apply intervalIntegral.integral_congr_ae
  filter_upwards [hr] with t ht hmem
  have hmemb : t ∈ uIcc a b := uIoc_subset_uIcc hmem
  exact ((regularizedEntropy_hasDerivAt hm he hδ (hFn t hmemb)).comp t (ht hmemb)).deriv.symm

end BoltzmannNonuniqueness

end

end

section

/-! # The entropy balance for an integral characteristic path -/

noncomputable section

open MeasureTheory Set

namespace BoltzmannNonuniqueness

theorem regularizedEntropy_integral_path {a b m e δ R A : ℝ} {r : ℝ → ℝ}
    (hm : 0 < m) (he : 0 < e) (hδ : 0 < δ) (hR : 0 ≤ R)
    (hr : IntervalIntegrable r volume a b)
    (hn : ∀ t ∈ uIcc a b, 0 ≤ A+∫ s in a..t, r s)
    (hb : ∀ t ∈ uIcc a b, A+(∫ s in a..t, r s) ≤ R) :
    (∫ t in a..b, Real.log (((A+∫ s in a..t, r s)+δ*e)/m)*r t) =
      regularizedEntropy m e δ (A+∫ s in a..b, r s)-regularizedEntropy m e δ A := by
  have hprimitive := hr.absolutelyContinuousOnInterval_intervalIntegral
    (left_mem_uIcc : a ∈ uIcc a b)
  have hconstant : AbsolutelyContinuousOnInterval (fun _ : ℝ => A) a b := by
    simpa only [AbsolutelyContinuousOnInterval,dist_self,Finset.sum_const_zero] using
      (tendsto_const_nhds : Filter.Tendsto (fun _ : ℕ × (ℕ → ℝ × ℝ) => (0:ℝ)) _ _)
  have hp : AbsolutelyContinuousOnInterval (fun t => A+∫ s in a..t, r s) a b :=
    hconstant.add hprimitive
  have hd : ∀ᵐ t, t ∈ uIcc a b →
      HasDerivAt (fun t => A+∫ s in a..t, r s) (r t) t := by
    filter_upwards [hr.ae_hasDerivAt_integral] with t ht hmem
    exact (ht hmem a left_mem_uIcc).const_add A
  simpa only [intervalIntegral.integral_same,add_zero] using
    regularizedEntropy_chain_rule hm he hδ hR hp hn hb hd

end BoltzmannNonuniqueness

end

end

section

/-! # Almost-everywhere bounds suffice for the entropy chain rule on a free path -/

noncomputable section

open MeasureTheory Set

namespace BoltzmannNonuniqueness

theorem continuous_path_bounds_of_ae {T R : ℝ} {F : ℝ → ℝ}
    (hT : 0 < T) (hR : 0 ≤ R) (hF : ContinuousOn F (Icc 0 T))
    (hae : ∀ᵐ t ∂volume.restrict (Icc 0 T), F t ∈ Icc 0 R) :
    ∀ t ∈ Icc 0 T, F t ∈ Icc 0 R := by
  let G : ℝ → ℝ := fun t => max 0 (min R (F t))
  have hG : ContinuousOn G (Icc 0 T) := continuousOn_const.sup (continuousOn_const.inf hF)
  have he : F =ᵐ[volume.restrict (Icc 0 T)] G := by
    filter_upwards [hae] with t ht
    dsimp [G]
    rw [min_eq_right ht.2,max_eq_right ht.1]
  have heq := Measure.eqOn_Icc_of_ae_eq volume hT.ne he hF hG
  intro t ht
  rw [heq ht]
  exact ⟨le_max_left _ _,max_le hR (min_le_left _ _)⟩

theorem regularizedEntropy_integral_path_of_ae_bounds {T m e δ R A : ℝ} {r : ℝ → ℝ}
    (hT : 0 < T) (hm : 0 < m) (he : 0 < e) (hδ : 0 < δ) (hR : 0 ≤ R)
    (hr : IntervalIntegrable r volume 0 T)
    (hbound : ∀ᵐ t ∂volume.restrict (Icc 0 T), (A+∫ s in 0..t, r s) ∈ Icc 0 R) :
    (∫ t in 0..T, Real.log (((A+∫ s in 0..t, r s)+δ*e)/m)*r t) =
      regularizedEntropy m e δ (A+∫ s in 0..T, r s)-regularizedEntropy m e δ A := by
  have hc : ContinuousOn (fun t => A+∫ s in 0..t, r s) (Icc 0 T) := by
    have h := intervalIntegral.continuousOn_primitive_interval' hr
      (left_mem_uIcc : (0:ℝ) ∈ uIcc 0 T)
    rw [uIcc_of_le hT.le] at h
    exact continuousOn_const.add h
  have hb := continuous_path_bounds_of_ae hT hR hc hbound
  apply regularizedEntropy_integral_path hm he hδ hR hr
  · simpa only [uIcc_of_le hT.le] using fun t ht => (hb t ht).1
  · simpa only [uIcc_of_le hT.le] using fun t ht => (hb t ht).2

end BoltzmannNonuniqueness

end

end

section

/-! # Integrating the entropy chain rule over the characteristic labels -/

noncomputable section

open MeasureTheory Set

namespace BoltzmannNonuniqueness

def entropyPath (a : Phase → ℝ) (r : ℝ × Phase → ℝ) (t : ℝ) (p : Phase) : ℝ :=
  a p+∫ s in 0..t, r (s,p)

theorem entropy_integral_balance {T δ : ℝ} (hT : 0 < T) (hδ : 0 < δ)
    (a m e R : Phase → ℝ) (r : ℝ × Phase → ℝ)
    (hm : ∀ p, 0 < m p) (he : ∀ p, 0 < e p) (hR : ∀ p, 0 ≤ R p)
    (hri : Integrable r ((volume.restrict (Icc 0 T)).prod volume))
    (hbound : ∀ᵐ p : Phase, ∀ᵐ t ∂volume.restrict (Icc 0 T),
      entropyPath a r t p ∈ Icc 0 (R p))
    (hET : Integrable (fun p => regularizedEntropy (m p) (e p) δ (entropyPath a r T p)))
    (hE0 : Integrable (fun p => regularizedEntropy (m p) (e p) δ (a p)))
    (hLi : Integrable (fun z : ℝ × Phase =>
      Real.log ((entropyPath a r z.1 z.2+δ*e z.2)/m z.2)*r z)
      ((volume.restrict (Icc 0 T)).prod volume)) :
    (∫ p : Phase, regularizedEntropy (m p) (e p) δ (entropyPath a r T p))-
      (∫ p : Phase, regularizedEntropy (m p) (e p) δ (a p)) =
    ∫ z : ℝ × Phase, Real.log ((entropyPath a r z.1 z.2+δ*e z.2)/m z.2)*r z
      ∂(volume.restrict (Icc 0 T)).prod volume := by
  have hp : ∀ᵐ p : Phase,
      regularizedEntropy (m p) (e p) δ (entropyPath a r T p)-
        regularizedEntropy (m p) (e p) δ (a p) =
      ∫ t, Real.log ((entropyPath a r t p+δ*e p)/m p)*r (t,p) ∂volume.restrict (Icc 0 T) := by
    filter_upwards [hri.prod_left_ae,hbound] with p hp hb
    have hpr : IntervalIntegrable (fun t => r (t,p)) volume 0 T :=
      (intervalIntegrable_iff_integrableOn_Icc_of_le hT.le).mpr hp
    have h := regularizedEntropy_integral_path_of_ae_bounds hT (hm p) (he p) hδ (hR p) hpr hb
    rw [intervalIntegral.integral_of_le hT.le,← integral_Icc_eq_integral_Ioc] at h
    exact h.symm
  calc
    _ = ∫ p : Phase, regularizedEntropy (m p) (e p) δ (entropyPath a r T p)-
        regularizedEntropy (m p) (e p) δ (a p) := (integral_sub hET hE0).symm
    _ = ∫ p : Phase, ∫ t, Real.log ((entropyPath a r t p+δ*e p)/m p)*r (t,p)
        ∂volume.restrict (Icc 0 T) := integral_congr_ae hp
    _ = _ := (integral_prod_symm _ hLi).symm

end BoltzmannNonuniqueness

end

end

end OAI
