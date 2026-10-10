import Mathlib
import OAI.Probability.SLE.StoppedPower

namespace OAI

/-! Swallow Exit for chordal SLE. -/

section
section

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge

lemma nonnegative_integral_tail {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (Y : Ω → ℝ) (hYi : Integrable Y P) (hY0 : ∀ ω, 0 ≤ Y ω)
    (M a : ℝ) (ha : 0 < a) (hmean : (∫ ω, Y ω ∂P) ≤ M) :
    P {ω | a ≤ Y ω} ≤ ENNReal.ofReal (M/a) := by
  have hmark := meas_ge_le_lintegral_div hYi.aemeasurable.ennreal_ofReal
    (ne_of_gt (ENNReal.ofReal_pos.mpr ha)) ENNReal.ofReal_ne_top
  calc
    P {ω | a ≤ Y ω} ≤ P {ω | ENNReal.ofReal a ≤ ENNReal.ofReal (Y ω)} :=
      measure_mono (fun ω hω => ENNReal.ofReal_le_ofReal hω)
    _ ≤ (∫⁻ ω, ENNReal.ofReal (Y ω) ∂P) / ENNReal.ofReal a := hmark
    _ = ENNReal.ofReal (∫ ω, Y ω ∂P) / ENNReal.ofReal a := by
      rw [ofReal_integral_eq_lintegral_ofReal hYi (Eventually.of_forall hY0)]
    _ ≤ ENNReal.ofReal M / ENNReal.ofReal a :=
      ENNReal.div_le_div_right (ENNReal.ofReal_le_ofReal hmean) _
    _ = ENNReal.ofReal (M/a) := (ENNReal.ofReal_div_of_pos ha).symm

namespace RadialLocalization
variable {Ω : Type*} [MeasurableSpace Ω]
    {B : ℝ≥0 → Ω → ℝ} {hm : ∀ t, Measurable (B t)}
    {κ lo hi : ℝ} {hle : lo ≤ hi} {q₀ : ℂ × ℝ}
    {c : ClippedLogSolution B hm κ lo hi hle q₀} {R : ℝ} {T : ℝ≥0}

lemma exit_probability {P : Measure Ω}
    (a : RadialLocalization c R T)
    (hB : IsBrownianReal B P)
    (hBm : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2))
    (hBc : ∀ ω, Continuous (fun t => B t ω))
    (hκ : 4 < κ) (hR : 0 < R) (hhi : q₀.1.im ≤ hi)
    (b : ℝ) (hb : 0 < b)
    (hbR : b ≤ Real.exp (((κ-4)/(2*κ))*Real.log R))
    (hbT : b ≤ (((κ-4)/(2*κ))*((κ-4)/4)*Real.exp ((((κ-4)/(2*κ))-2)*Real.log R)) * T) :
    P {ω | a.τ ω = T ∨ greenLogNormSq κ (c.Q (a.τ ω) ω) (B (a.τ ω) ω) = R^2} ≤
      ENNReal.ofReal (swallowLyapunov κ ((κ-4)/(2*κ)) (3*(κ-4)/8) q₀ 0 / b) := by
  let : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  let β := (κ-4)/(2*κ)
  let C := 3*(κ-4)/8
  let d := β*((κ-4)/4)*Real.exp ((β-2)*Real.log R)
  let F (ω : Ω) := swallowLyapunov κ β C (c.Q (a.τ ω) ω) (B (a.τ ω) ω)
  let Y (ω : Ω) := F ω + d*(a.τ ω : ℝ)
  have hk : 0 < κ := lt_trans (by norm_num) hκ
  have hβ : 0 < β := by dsimp [β]; positivity
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hd : 0 ≤ d := by dsimp [d]; positivity
  have hF0 (ω : Ω) : 0 ≤ F ω := swallowLyapunov_nonneg κ β C hC _ _
  have hY0 (ω : Ω) : 0 ≤ Y ω := add_nonneg (hF0 ω) (mul_nonneg hd (a.τ ω).coe_nonneg)
  have hmean := a.stopped_lyapunov_bound hB hBm hBc hκ hR hhi
  have hτi : Integrable (fun ω => (a.τ ω : ℝ)) P :=
    bounded_nnreal_integrable a.τ (stopping_time_measurable_nnreal a.stopping) T a.bounded
  have hYi : Integrable Y P := hmean.1.add (hτi.const_mul d)
  have hYmean : (∫ ω, Y ω ∂P) ≤ swallowLyapunov κ β C q₀ 0 := by
    rw [show (∫ ω, Y ω ∂P) = (∫ ω, F ω ∂P)+d*(∫ ω, (a.τ ω : ℝ) ∂P) by
      rw [show Y = fun ω => F ω+d*(a.τ ω : ℝ) from rfl,
        integral_add hmean.1 (hτi.const_mul d), integral_const_mul]]
    exact hmean.2
  apply (measure_mono (show {ω | a.τ ω = T ∨ greenLogNormSq κ (c.Q (a.τ ω) ω) (B (a.τ ω) ω) = R^2}
      ⊆ {ω | b ≤ Y ω} from ?_)).trans (nonnegative_integral_tail Y hYi hY0 _ b hb hYmean)
  intro ω hω
  rcases hω with ht | hn
  · change b ≤ F ω+d*(a.τ ω : ℝ)
    rw [ht]
    exact hbT.trans (le_add_of_nonneg_left (hF0 ω))
  · have hr := radialLogPower_at_boundary κ β (c.Q (a.τ ω) ω) (B (a.τ ω) ω) R hn
    have hh : Real.exp (β*Real.log R) ≤ F ω := by
      change Real.exp (β*Real.log R) ≤ radialLogPower κ β _ _ + C*heightLogPower β _
      rw [hr]
      exact le_add_of_nonneg_right (mul_nonneg hC (heightLogPower_pos β _).le)
    exact (hbR.trans hh).trans (le_add_of_nonneg_right (mul_nonneg hd (a.τ ω).coe_nonneg))

end RadialLocalization
end SLEExactGauge
end

 
section

open Set Filter MeasureTheory ProbabilityTheory Complex
open scoped Topology NNReal ENNReal
namespace SLEExactGauge

 

structure BoundaryLocalization
    {Ω : Type*} [MeasurableSpace Ω]
    {B : ℝ≥0 → Ω → ℝ} {hm : ∀ t, Measurable (B t)}
    {κ a : ℝ} {q₀ : ℂ} (c : BoundaryClockSolution B hm κ a q₀)
    (α β R H : ℝ) (T : ℝ≥0) where
  τ : Ω → ℝ≥0
  stopping : IsStoppingTime (Filtration.natural B (fun t => (hm t).stronglyMeasurable))
    (fun ω => (τ ω : WithTop ℝ≥0))
  bounded : ∀ ω, τ ω ≤ T
  inside : ∀ ω t, t ≤ τ ω → ‖(c.Q t ω,B t ω)‖ ≤ R ∧
    3*a ≤ (c.Q t ω).re-Real.sqrt κ*B t ω ∧
    boundaryDensity κ α β (c.Q t ω) (B t ω) ≤ H
  before : ∀ ω t, t < τ ω → ‖(c.Q t ω,B t ω)‖ < R ∧
    3*a < (c.Q t ω).re-Real.sqrt κ*B t ω ∧
    boundaryDensity κ α β (c.Q t ω) (B t ω) < H
  boundary : ∀ ω, τ ω < T → ‖(c.Q (τ ω) ω,B (τ ω) ω)‖ = R ∨
    (c.Q (τ ω) ω).re-Real.sqrt κ*B (τ ω) ω = 3*a ∨
    boundaryDensity κ α β (c.Q (τ ω) ω) (B (τ ω) ω) = H

lemma exists_boundaryLocalization
    {Ω : Type*} [MeasurableSpace Ω]
    {B : ℝ≥0 → Ω → ℝ} {hm : ∀ t, Measurable (B t)}
    (hBc : ∀ ω, Continuous (fun t => B t ω)) (hB0 : ∀ ω, B 0 ω = 0)
    {κ a : ℝ} {q₀ : ℂ} (c : BoundaryClockSolution B hm κ a q₀)
    (ha : 0 < a) (α β R H : ℝ) (T : ℝ≥0)
    (hR : ‖(q₀,(0:ℝ))‖ ≤ R) (hx : 3*a ≤ q₀.re)
    (hH : boundaryDensity κ α β q₀ 0 ≤ H) :
    Nonempty (BoundaryLocalization c α β R H T) := by
  let f := Filtration.natural B (fun t => (hm t).stronglyMeasurable)
  let V (p : ℂ × ℝ) := min (R-‖p‖) (min (p.1.re-Real.sqrt κ*p.2-3*a)
    (H-smoothBoundaryDensity κ α β a p.1 p.2))
  have hVc : Continuous V := by
    exact (continuous_const.sub continuous_norm).min
      (((Complex.continuous_re.comp continuous_fst).sub (continuous_const.mul continuous_snd)).sub
        continuous_const |>.min (continuous_const.sub (smoothBoundaryDensity_contDiff κ α β ha).continuous))
  let D (t : ℝ≥0) (ω : Ω) := V (c.Q t ω,B t ω)
  have hBa : Adapted f B :=
    (Filtration.stronglyAdapted_natural (fun t => (hm t).stronglyMeasurable)).adapted
  have hDa : Adapted f D := fun t => hVc.measurable.comp ((c.adapted t).prodMk (hBa t))
  have hDc (ω : Ω) : Continuous (fun t => D t ω) :=
    hVc.comp (((c.lipschitz ω).continuous.comp NNReal.continuous_coe).prodMk (hBc ω))
  have hD0 (ω : Ω) : 0 ≤ D 0 ω := by
    have he : smoothBoundaryDensity κ α β a q₀ 0 = boundaryDensity κ α β q₀ 0 :=
      smoothBoundaryDensity_eq ha (by simpa using (show 2*a ≤ q₀.re by linarith))
    simpa only [D,V,NNReal.coe_zero,c.initial,hB0,mul_zero,sub_zero,he,
      le_min_iff,sub_nonneg] using And.intro hR (And.intro hx hH)
  obtain ⟨τ,hτ,hb,hin,hpre,hbd⟩ := first_margin_stopping f D hDa hDc hD0 T
  have hin' (ω : Ω) (t : ℝ≥0) (ht : t ≤ τ ω) : ‖(c.Q t ω,B t ω)‖ ≤ R ∧
      3*a ≤ (c.Q t ω).re-Real.sqrt κ*B t ω ∧ boundaryDensity κ α β (c.Q t ω) (B t ω) ≤ H := by
    have hh := hin ω t ht
    simp only [D,V,le_min_iff,sub_nonneg] at hh
    rw [smoothBoundaryDensity_eq ha (by linarith [hh.2.1])] at hh
    exact hh
  refine ⟨⟨τ,hτ,hb,hin',?_,?_⟩⟩
  · intro ω t ht
    have hh := hpre ω t ht
    simp only [D,V,lt_min_iff,sub_pos] at hh
    rw [smoothBoundaryDensity_eq ha (by linarith [hh.2.1])] at hh
    exact hh
  · intro ω ht
    have hh := hbd ω ht
    dsimp only [D,V] at hh
    rw [smoothBoundaryDensity_eq ha (by linarith [(hin' ω (τ ω) le_rfl).2.1])] at hh
    rw [min_eq_iff] at hh
    rcases hh with ⟨hh,_⟩ | ⟨hh,_⟩
    · exact Or.inl (sub_eq_zero.mp hh).symm
    · rw [min_eq_iff] at hh
      rcases hh with ⟨hh,_⟩ | ⟨hh,_⟩
      · exact Or.inr (Or.inl (sub_eq_zero.mp hh))
      · exact Or.inr (Or.inr (sub_eq_zero.mp hh).symm)

namespace BoundaryLocalization
variable {Ω : Type*} [MeasurableSpace Ω]
    {B : ℝ≥0 → Ω → ℝ} {hm : ∀ t, Measurable (B t)}
    {κ a : ℝ} {q₀ : ℂ} {c : BoundaryClockSolution B hm κ a q₀}
    {α β R H : ℝ} {T : ℝ≥0}

lemma density_crossing_probability {P : Measure Ω}
    (l : BoundaryLocalization c α β R H T)
    (hB : IsBrownianReal B P)
    (hBm : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2))
    (hBc : ∀ ω, Continuous (fun t => B t ω))
    (hκ : 0 < κ) (ha : 0 < a) (hβ : -α-2+κ*(β+1)/2=0)
    (hR : 0 ≤ R) (hH : 0 < H) :
    P {ω | H ≤ boundaryDensity κ α β (c.Q (l.τ ω) ω) (B (l.τ ω) ω)} ≤
      ENNReal.ofReal (boundaryDensity κ α β q₀ 0/H) := by
  obtain ⟨hi,he⟩ := c.stopped_boundary_density hB hBm hBc hκ ha α β hβ R hR
    l.τ l.stopping T l.bounded (fun ω t ht =>
      ⟨(l.inside ω t ht).1,by linarith [(l.inside ω t ht).2.1]⟩)
  exact nonnegative_integral_tail _ hi (fun ω => (Real.exp_pos _).le) _ _ hH he.le

end BoundaryLocalization
end SLEExactGauge
end

 
section

open Set Filter MeasureTheory Complex
open scoped Topology NNReal
namespace SLEExactGauge

 

def IsPositiveBoundaryClockPath (U : ℝ≥0 → ℝ) (x : ℝ) (T : ℝ≥0) (Q : ℝ → ℂ) : Prop :=
  Q 0 = (x:ℂ) ∧
  (∀ t ∈ Icc 0 (T:ℝ), 0 < (Q t).re-U t.toNNReal) ∧
  (∀ t ∈ Icc 0 (T:ℝ), HasDerivWithinAt Q
    (((2/((Q t).re-U t.toNNReal):ℝ):ℂ)+
      (((Q t).re-U t.toNNReal)⁻¹^2:ℝ)*I) (Icc 0 (T:ℝ)) t)

namespace IsPositiveBoundaryClockPath
variable {U : ℝ≥0 → ℝ} {x : ℝ} {T : ℝ≥0} {Q : ℝ → ℂ}

lemma continuousOn (h : IsPositiveBoundaryClockPath U x T Q) :
    ContinuousOn Q (Icc 0 (T:ℝ)) := fun t ht => (h.2.2 t ht).continuousWithinAt

lemma positive_lower_bound (h : IsPositiveBoundaryClockPath U x T Q) (hU : Continuous U) :
    ∃ a : ℝ, 0 < a ∧ ∀ t ∈ Icc 0 (T:ℝ), a ≤ (Q t).re-U t.toNNReal := by
  have hc : ContinuousOn (fun t : ℝ => (Q t).re-U t.toNNReal) (Icc 0 (T:ℝ)) :=
    (Complex.continuous_re.comp_continuousOn h.continuousOn).sub
      ((hU.comp continuous_real_toNNReal).continuousOn)
  obtain ⟨s,hs,hmin⟩ := (isCompact_Icc : IsCompact (Icc 0 (T:ℝ))).exists_isMinOn
    ⟨0,le_rfl,T.coe_nonneg⟩ hc
  exact ⟨_,h.2.1 s hs,fun t ht => hmin ht⟩

lemma clock_identity (h : IsPositiveBoundaryClockPath U x T Q) (hU : Continuous U) :
    (Q T).im = ∫ t in (0:ℝ)..(T:ℝ), ((Q t).re-U t.toNNReal)⁻¹^2 := by
  have hc : ContinuousOn (fun t : ℝ => ((Q t).re-U t.toNNReal)⁻¹^2) (Icc 0 (T:ℝ)) :=
    (((Complex.continuous_re.comp_continuousOn h.continuousOn).sub
      ((hU.comp continuous_real_toNNReal).continuousOn)).inv₀ (fun t ht => (h.2.1 t ht).ne')).pow 2
  have hd (t : ℝ) (ht : t ∈ Icc 0 (T:ℝ)) : HasDerivWithinAt (fun u => (Q u).im)
      (((Q t).re-U t.toNNReal)⁻¹^2) (Icc 0 (T:ℝ)) t := by
    simpa only [Function.comp_def,ContinuousLinearMap.comp_apply,Complex.imCLM_apply,Complex.add_im,
      Complex.ofReal_im,Complex.mul_im,Complex.ofReal_re,Complex.I_im,mul_one,
      Complex.I_re,mul_zero,add_zero,zero_add] using
      Complex.imCLM.hasFDerivAt.comp_hasDerivWithinAt t (h.2.2 t ht)
  have hdr (t : ℝ) (ht : t ∈ Ioo 0 (T:ℝ)) : HasDerivWithinAt (fun u => (Q u).im)
      (((Q t).re-U t.toNNReal)⁻¹^2) (Ioi t) t := by
    exact (hasDerivWithinAt_Ici_of_Icc ⟨ht.1.le,ht.2⟩
      (hd t ⟨ht.1.le,ht.2.le⟩)).mono Ioi_subset_Ici_self
  have he := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le T.coe_nonneg
    (Complex.continuous_im.comp_continuousOn h.continuousOn) hdr
    (hc.intervalIntegrable_of_Icc T.coe_nonneg)
  dsimp only [Function.comp_def] at he
  rw [h.1,Complex.ofReal_im,sub_zero] at he
  exact he.symm

lemma clipped_identification
    {Ω : Type*} [MeasurableSpace Ω] {B : ℝ≥0 → Ω → ℝ}
    {hm : ∀ t, Measurable (B t)} {κ a : ℝ}
    (c : BoundaryClockSolution B hm κ a (x:ℂ)) (ha : 0 < a) (ω : Ω)
    (h : IsPositiveBoundaryClockPath (fun t => Real.sqrt κ*B t ω) x T Q)
    (hgap : ∀ t ∈ Icc 0 (T:ℝ), a ≤ (Q t).re-Real.sqrt κ*B t.toNNReal ω) :
    EqOn Q (fun t => c.Q t ω) (Icc 0 (T:ℝ)) := by
  have hd (t : ℝ) (ht : t ∈ Icc 0 (T:ℝ)) : HasDerivWithinAt Q
      (boundaryClockField a (Real.sqrt κ*B t.toNNReal ω) (Q t)) (Icc 0 (T:ℝ)) t := by
    simpa only [boundaryClockField,positiveBoundaryField_eq (hgap t ht),max_eq_right (hgap t ht)] using h.2.2 t ht
  have hc (t : ℝ) (ht : t ∈ Icc 0 (T:ℝ)) := (c.derivative ω t ht.1).mono
    (show Icc (0:ℝ) (T:ℝ) ⊆ Ici 0 from fun s hs => hs.1)
  apply ODE_solution_unique (fun t => boundaryClockField_lipschitz ha (Real.sqrt κ*B t.toNNReal ω))
    h.continuousOn
    (fun t ht => hasDerivWithinAt_Ici_of_Icc ht (hd t ⟨ht.1,ht.2.le⟩))
    (c.lipschitz ω).continuous.continuousOn
    (fun t ht => hasDerivWithinAt_Ici_of_Icc ht (hc t ⟨ht.1,ht.2.le⟩))
  exact h.1.trans (c.initial ω).symm

end IsPositiveBoundaryClockPath
end SLEExactGauge
end

 
section

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge

 

noncomputable def greenDensity (κ : ℝ) (U : ℝ≥0 → ℝ) (γ : ℝ≥0 → ℂ)
    (G : ℝ≥0 → ℂ → ℂ) (t : ℝ≥0) (z : ℂ) : ℝ := by
  classical
  exact if z ∈ survivingDomain γ t then
    (fullRadius G t z) ^ (-codimension κ) *
      (Real.sin (Complex.arg (G t z - (U t : ℂ)))) ^ greenExponent κ
  else 0

noncomputable def initialGreen (κ : ℝ) (z : ℂ) : ℝ :=
  (2 * z.im) ^ (-codimension κ) *
    (Real.sin (Complex.arg z)) ^ greenExponent κ

 

noncomputable def radiusLevelTime (γ : ℝ≥0 → ℂ) (G : ℝ≥0 → ℂ → ℂ)
    (z : ℂ) (u : ℝ) : ℝ≥0∞ :=
  sInf {s : ℝ≥0∞ | s < ∞ ∧ z ∈ survivingDomain γ s.toNNReal ∧
    fullRadius G s.toNNReal z = (2 * z.im) * Real.exp (-u)}

 
noncomputable def stoppedGreen (κ : ℝ) (U : ℝ≥0 → ℝ) (γ : ℝ≥0 → ℂ)
    (G : ℝ≥0 → ℂ → ℂ) (z : ℂ) (u : ℝ) : ℝ :=
  if radiusLevelTime γ G z u < ∞ then
    greenDensity κ U γ G (radiusLevelTime γ G z u).toNNReal z
  else 0

lemma logCoordinates_re (G : ℝ≥0 → ℂ → ℂ) (z : ℂ) (t : ℝ≥0) :
    (logLoewnerCoordinates G z t).1.re = (G t z).re := by
  simp only [logLoewnerCoordinates, Real.toNNReal_coe, Complex.add_re, Complex.ofReal_re,
    Complex.mul_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul,
    sub_self, add_zero]

lemma logCoordinates_im (G : ℝ≥0 → ℂ → ℂ) (z : ℂ) (t : ℝ≥0) :
    (logLoewnerCoordinates G z t).1.im = Real.log (G t z).im := by
  simp only [logLoewnerCoordinates, Real.toNNReal_coe, Complex.add_im, Complex.ofReal_im,
    Complex.mul_im, Complex.ofReal_re, Complex.I_re, Complex.I_im, mul_zero, mul_one,
    add_zero, zero_add]

lemma logCoordinates_snd (G : ℝ≥0 → ℂ → ℂ) (z : ℂ) (t : ℝ≥0) :
    (logLoewnerCoordinates G z t).2 = Real.log ‖deriv (G t) z‖ := by
  simp only [logLoewnerCoordinates, Real.toNNReal_coe]

lemma greenLogNormSq_logCoordinates (κ b : ℝ) (G : ℝ≥0 → ℂ → ℂ) (z : ℂ) (t : ℝ≥0)
    (hy : 0 < (G t z).im) :
    greenLogNormSq κ (logLoewnerCoordinates G z t) b =
      Complex.normSq (G t z - ((Real.sqrt κ * b : ℝ) : ℂ)) := by
  have he : Real.exp (2 * Real.log (G t z).im) = (G t z).im ^ 2 := by
    rw [show 2 * Real.log (G t z).im = Real.log (G t z).im + Real.log (G t z).im by ring,
      Real.exp_add, Real.exp_log hy, pow_two]
  rw [greenLogNormSq, logCoordinates_re, logCoordinates_im, he]
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.ofReal_re,
    Complex.ofReal_im, sub_zero, pow_two]

lemma logAngleSq_logCoordinates (κ b : ℝ) (G : ℝ≥0 → ℂ → ℂ) (z : ℂ) (t : ℝ≥0)
    (hy : 0 < (G t z).im) :
    logAngleSq κ (logLoewnerCoordinates G z t) b =
      (Real.sin (Complex.arg (G t z - ((Real.sqrt κ * b : ℝ) : ℂ)))) ^ 2 := by
  rw [logAngleSq, greenLogNormSq_logCoordinates κ b G z t hy, logCoordinates_im,
    Complex.sin_arg, Complex.normSq_eq_norm_sq, div_pow]
  congr 1
  simp only [Complex.sub_im, Complex.ofReal_im, sub_zero]
  rw [show 2 * Real.log (G t z).im = Real.log (G t z).im + Real.log (G t z).im by ring,
    Real.exp_add, Real.exp_log hy, pow_two]

lemma greenLogDensity_logCoordinates
    {U : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}
    (hU : Continuous U) (h : IsCapacityTwoWitness U γ G F)
    (κ b : ℝ) (z : ℂ) (t : ℝ≥0) (hz : z ∈ survivingDomain γ t)
    (hUb : U t = Real.sqrt κ * b) :
    greenLogDensity κ (logLoewnerCoordinates G z t) b = greenDensity κ U γ G t z := by
  have hy := h.imag_positive t z hz
  have hj := h.derivative_norm_positive hU t z hz
  have hn : 0 < ‖G t z - ((Real.sqrt κ * b : ℝ) : ℂ)‖ := by
    apply norm_pos_iff.mpr
    simpa only [hUb] using h.centered_ne_zero t z hz
  have hs : 0 < Real.sin (Complex.arg (G t z - (U t : ℂ))) := by
    rw [Complex.sin_arg, Complex.sub_im, Complex.ofReal_im, sub_zero, hUb]
    exact div_pos hy hn
  have hR := h.fullRadius_positive hU t z hz
  have hlogR : Real.log (fullRadius G t z) =
      Real.log 2 + Real.log (G t z).im - Real.log ‖deriv (G t) z‖ := by
    rw [fullRadius, Real.log_div (mul_ne_zero (by norm_num) hy.ne') hj.ne',
      Real.log_mul (by norm_num) hy.ne']
  have hlogS : Real.log (Real.sin (Complex.arg (G t z - (U t : ℂ)))) =
      Real.log (G t z).im - Real.log ‖G t z - ((Real.sqrt κ * b : ℝ) : ℂ)‖ := by
    rw [Complex.sin_arg, Complex.sub_im, Complex.ofReal_im, sub_zero, hUb,
      Real.log_div hy.ne' hn.ne']
  rw [greenDensity, ite_eq_left hz, Real.rpow_def_of_pos hR, Real.rpow_def_of_pos hs,
    ← Real.exp_add, hlogR, hlogS, greenLogDensity, logCoordinates_im, logCoordinates_snd,
    greenLogNormSq_logCoordinates κ b G z t hy, Complex.normSq_eq_norm_sq, Real.log_pow]
  congr 1
  push_cast
  ring

lemma greenLogDensity_initial (κ : ℝ) (z : ℂ) (hz : z ∈ upperHalfPlane) :
    greenLogDensity κ (initialLogCoordinates z) 0 = initialGreen κ z := by
  have hn : 0 < ‖z‖ := norm_pos_iff.mpr (by
    have hp : 0 < z.im := hz
    intro he; simp only [he, Complex.zero_im, lt_self_iff_false] at hp)
  have hs : 0 < Real.sin (Complex.arg z) := by rw [Complex.sin_arg]; exact div_pos hz hn
  have he : Real.exp (2 * Real.log z.im) = z.im ^ 2 := by
    rw [show 2 * Real.log z.im = Real.log z.im + Real.log z.im by ring,
      Real.exp_add, Real.exp_log hz, pow_two]
  have hN : greenLogNormSq κ (initialLogCoordinates z) 0 = Complex.normSq z := by
    simp only [greenLogNormSq, initialLogCoordinates, Complex.add_re, Complex.ofReal_re,
      Complex.mul_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero,
      sub_self, add_zero, sub_zero, Complex.add_im, Complex.mul_im, mul_one, zero_add, he,
      Complex.normSq_apply, pow_two]
  rw [initialGreen, Real.rpow_def_of_pos (mul_pos (by norm_num) hz), Real.rpow_def_of_pos hs,
    ← Real.exp_add, Real.log_mul (by norm_num) hz.ne', Complex.sin_arg, Real.log_div hz.ne' hn.ne']
  rw [greenLogDensity, hN, Complex.normSq_eq_norm_sq, Real.log_pow]
  simp only [initialLogCoordinates, Complex.add_im, Complex.ofReal_im, Complex.mul_im,
    Complex.ofReal_re, Complex.I_im, Complex.I_re, mul_one, mul_zero, zero_add, add_zero,
    Nat.cast_ofNat]
  congr 1
  ring

end SLEExactGauge
end

 
section

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
namespace RadialLocalization
variable {Ω : Type*} [MeasurableSpace Ω]
    {B : ℝ≥0 → Ω → ℝ} {hm : ∀ t, Measurable (B t)}
    {κ lo hi : ℝ} {hle : lo ≤ hi} {q₀ : ℂ × ℝ}
    {c : ClippedLogSolution B hm κ lo hi hle q₀} {R : ℝ} {T : ℝ≥0}

lemma alive_forces_radial_or_time_boundary (a : RadialLocalization c R T)
    (hBc : ∀ ω, Continuous (fun t => B t ω)) {z : ℂ} (hz : z ∈ upperHalfPlane)
    (hq : q₀ = initialLogCoordinates z) (hhi : q₀.1.im ≤ hi)
    (ω : Ω) (γ : ℝ≥0 → ℂ) (G F : ℝ≥0 → ℂ → ℂ)
    (hw : IsCapacityTwoWitness (fun t => Real.sqrt κ*B t ω) γ G F)
    (hlive : z ∈ survivingDomain γ T) (hlo : lo < Real.log (G T z).im) :
    a.τ ω = T ∨ greenLogNormSq κ (c.Q (a.τ ω) ω) (B (a.τ ω) ω) = R^2 := by
  rcases eq_or_lt_of_le (a.bounded ω) with h | h
  · exact Or.inl h
  rcases a.boundary ω h with hN | hh
  · exact Or.inr hN
  obtain ⟨_,he⟩ := a.chart_identification hBc hz hq hhi ω γ G F hw
  have hheight := (hw.log_height_bounds T z hlive (a.τ ω)
    ⟨(a.τ ω).coe_nonneg, NNReal.coe_le_coe.mpr (a.bounded ω)⟩).1
  rw [he (a.τ ω) le_rfl, logCoordinates_im] at hh
  simp only [Real.toNNReal_coe] at hheight
  exact False.elim (not_le_of_gt hlo (hh ▸ hheight))

end RadialLocalization

lemma measure_eventually_sets_le {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (E : ℕ → Set Ω) (C : ℝ≥0∞) (hC : ∀ n, P (E n) ≤ C) :
    P {ω | ∀ᶠ n : ℕ in atTop, ω ∈ E n} ≤ C := by
  let H (n : ℕ) := ⋂ m ≥ n, E m
  have hH : Monotone H := by
    intro n m hnm ω hω
    simp only [H, mem_iInter] at hω ⊢
    exact fun k hk => hω k (hnm.trans hk)
  have he : {ω | ∀ᶠ n : ℕ in atTop, ω ∈ E n} = ⋃ n, H n := by
    ext ω
    simp only [mem_ofPred_eq, eventually_atTop, mem_iUnion, H, mem_iInter]
  rw [he, hH.measure_iUnion]
  apply iSup_le
  intro n
  apply (measure_mono (show H n ⊆ E n from fun ω hω => by
    exact mem_iInter.mp (mem_iInter.mp hω n) le_rfl)).trans (hC n)

end SLEExactGauge
end

 
section

open Set Filter MeasureTheory ProbabilityTheory Complex
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
namespace BoundaryLocalization
variable {Ω : Type*} [MeasurableSpace Ω]
    {B : ℝ≥0 → Ω → ℝ} {hm : ∀ t, Measurable (B t)}
    {κ a x : ℝ} {c : BoundaryClockSolution B hm κ a (x:ℂ)}
    {α β R H : ℝ} {T : ℝ≥0}

 

lemma true_crossing_forces_density_boundary
    (l : BoundaryLocalization c α β R H T) (ha : 0 < a)
    (ω : Ω) (S : ℝ≥0) (hS : S < T) (Q : ℝ → ℂ)
    (hQ : IsPositiveBoundaryClockPath (fun t => Real.sqrt κ*B t ω) x S Q)
    (hgap : ∀ t ∈ Icc 0 (S:ℝ), 3*a < (Q t).re-Real.sqrt κ*B t.toNNReal ω)
    (hbound : ∀ t : ℝ≥0, t ≤ S → ‖(Q t,B t ω)‖ < R)
    (hhit : H ≤ boundaryDensity κ α β (Q S) (B S ω)) :
    H ≤ boundaryDensity κ α β (c.Q (l.τ ω) ω) (B (l.τ ω) ω) := by
  have he := hQ.clipped_identification c ha ω (fun t ht => by linarith [hgap t ht])
  have hτS : l.τ ω ≤ S := by
    by_contra h
    have hpre := (l.before ω S (not_le.mp h)).2.2
    have heS : Q S = c.Q S ω := he ⟨S.coe_nonneg,le_rfl⟩
    rw [← heS] at hpre
    exact not_lt_of_ge hhit hpre
  have hτT : l.τ ω < T := hτS.trans_lt hS
  have heτ : Q (l.τ ω) = c.Q (l.τ ω) ω := he ⟨(l.τ ω).coe_nonneg,NNReal.coe_le_coe.mpr hτS⟩
  rcases l.boundary ω hτT with hnorm | hg | hf
  · have hb := hbound (l.τ ω) hτS
    rw [heτ,hnorm] at hb
    exact False.elim (lt_irrefl R hb)
  · have hp := hgap (l.τ ω) ⟨(l.τ ω).coe_nonneg,NNReal.coe_le_coe.mpr hτS⟩
    rw [Real.toNNReal_coe,heτ,hg] at hp
    exact False.elim (lt_irrefl _ hp)
  · exact hf.ge

end BoundaryLocalization
end SLEExactGauge
end

 
section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
 
theorem exists_measurable_brownian_version
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P) :
    ∃ C : ℝ≥0 → Ω → ℝ, (∀ t, Measurable (C t)) ∧ IsBrownianReal C P ∧
      (∀ᵐ ω ∂P, ∀ t, C t ω = B t ω) := by
  let b (n k : ℕ) : Ω → ℝ :=
    (hB.aemeasurable (stopGridTime n k)).mk (B (stopGridTime n k))
  have hb (n k : ℕ) : Measurable (b n k) := (hB.aemeasurable _).measurable_mk
  have heq : ∀ᵐ ω ∂P, ∀ n k, b n k ω = B (stopGridTime n k) ω := by
    apply ae_all_iff.mpr
    intro n
    apply ae_all_iff.mpr
    intro k
    exact (hB.aemeasurable _).ae_eq_mk.symm
  let C (t : ℝ≥0) (ω : Ω) : ℝ :=
    limUnder atTop (fun n => b n (stopGridIndex n t) ω)
  have hm (t : ℝ≥0) : Measurable (C t) :=
    (StronglyMeasurable.limUnder (fun n => (hb n _).stronglyMeasurable)).measurable
  have hCB : ∀ᵐ ω ∂P, ∀ t, C t ω = B t ω := by
    filter_upwards [hB.cont, heq] with ω hω heqω
    intro t
    change limUnder atTop (fun n => b n (stopGridIndex n t) ω) = B t ω
    simp_rw [heqω]
    exact (hω.continuousAt.tendsto.comp (stopGrid_tendsto t)).limUnder_eq
  refine ⟨C, hm, ⟨?_, ?_⟩, hCB⟩
  · exact hB.toIsPreBrownianReal.congr (fun t => hCB.mono fun ω hω => (hω t).symm)
  · filter_upwards [hB.cont, hCB] with ω hω heqω
    simpa only [heqω] using hω

 

theorem exists_continuous_measurable_brownian_version
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P) :
    ∃ C : ℝ≥0 → Ω → ℝ,
      Measurable (fun q : ℝ≥0 × Ω => C q.1 q.2) ∧
      (∀ ω, Continuous (fun t => C t ω)) ∧ IsBrownianReal C P ∧
      (∀ᵐ ω ∂P, ∀ t, C t ω = B t ω) := by
  classical
  obtain ⟨V, hVm, hV, hVB⟩ := exists_measurable_brownian_version hB
  let N := toMeasurable P {ω | ¬ Continuous (fun t => V t ω)}
  have hNm : MeasurableSet N := measurableSet_toMeasurable _ _
  have hN : P N = 0 := by
    rw [show N = toMeasurable P {ω | ¬ Continuous (fun t => V t ω)} from rfl,
      measure_toMeasurable]
    exact ae_iff.mp hV.cont
  let C (t : ℝ≥0) (ω : Ω) := if ω ∈ N then (0 : ℝ) else V t ω
  have hCm (t) : Measurable (C t) := measurable_const.piecewise hNm (hVm t)
  have hCc (ω) : Continuous (fun t => C t ω) := by
    by_cases hω : ω ∈ N
    · simpa only [C, ite_eq_left hω] using (continuous_const : Continuous (fun _ : ℝ≥0 => (0 : ℝ)))
    · have hv : Continuous (fun t => V t ω) := by
        by_contra hh
        exact hω (subset_toMeasurable P _ hh)
      simpa only [C, ite_eq_right hω] using hv
  have hCV : ∀ᵐ ω ∂P, ∀ t, C t ω = V t ω := by
    filter_upwards [show ∀ᵐ ω ∂P, ω ∉ N from (ae_iff.mpr (by simpa only [not_not, ofPred_mem_eq] using hN))] with ω hω
    intro t
    simp only [C, ite_eq_right hω]
  have hCB : ∀ᵐ ω ∂P, ∀ t, C t ω = B t ω := by
    filter_upwards [hCV, hVB] with ω hω hω'
    exact fun t => (hω t).trans (hω' t)
  refine ⟨C, measurable_uncurry_of_continuous_of_measurable hCc hCm, hCc, ?_, hCB⟩
  exact ⟨hV.toIsPreBrownianReal.congr (fun t => hCV.mono fun ω hω => (hω t).symm),
    Eventually.of_forall hCc⟩

 

theorem exists_regular_brownian_version
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P) :
    ∃ C : ℝ≥0 → Ω → ℝ,
      Measurable (fun q : ℝ≥0 × Ω => C q.1 q.2) ∧
      (∀ ω, Continuous (fun t => C t ω)) ∧ (∀ ω, C 0 ω = 0) ∧
      IsBrownianReal C P ∧ (∀ᵐ ω ∂P, ∀ t, C t ω = B t ω) := by
  obtain ⟨V, hVm, hVc, hV, hVB⟩ := exists_continuous_measurable_brownian_version hB
  let C (t : ℝ≥0) (ω : Ω) := V t ω - V 0 ω
  have hV0m : Measurable (V 0) := hVm.comp (measurable_const.prodMk measurable_id)
  have hCm : Measurable (fun q : ℝ≥0 × Ω => C q.1 q.2) :=
    hVm.sub (hV0m.comp measurable_snd)
  have hCc (ω : Ω) : Continuous (fun t => C t ω) := (hVc ω).sub continuous_const
  have hCV : ∀ᵐ ω ∂P, ∀ t, C t ω = V t ω := by
    filter_upwards [hV.eval_zero_ae_eq_zero] with ω h0
    intro t
    simp only [C, h0, sub_zero]
  refine ⟨C, hCm, hCc, fun ω => sub_self _, ?_, ?_⟩
  · exact ⟨hV.toIsPreBrownianReal.congr (fun t => hCV.mono fun ω hω => (hω t).symm),
      Eventually.of_forall hCc⟩
  · filter_upwards [hCV, hVB] with ω hω hω'
    exact fun t => (hω t).trans (hω' t)
end SLEExactGauge
end

 
section

open Set Filter MeasureTheory ProbabilityTheory Complex
open scoped Topology NNReal ENNReal
namespace SLEExactGauge

 

theorem boundary_maximal_density_regular
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hBm : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2))
    (hBc : ∀ ω, Continuous (fun t => B t ω)) (hB0 : ∀ ω, B 0 ω = 0)
    (κ α β x H : ℝ) (hκ : 0 < κ) (hx : 0 < x) (hH : 0 < H)
    (hβ : -α-2+κ*(β+1)/2=0)
    (hH0 : boundaryDensity κ α β (x:ℂ) 0 ≤ H) :
    P {ω | ∃ (T : ℝ≥0) (Q : ℝ → ℂ),
      IsPositiveBoundaryClockPath (fun t => Real.sqrt κ*B t ω) x T Q ∧
      H ≤ boundaryDensity κ α β (Q T) (B T ω)} ≤
      ENNReal.ofReal (boundaryDensity κ α β (x:ℂ) 0 / H) := by
  let hm (t) : Measurable (B t) := hBm.comp (measurable_const.prodMk measurable_id)
  let a (n : ℕ) : ℝ := (x/6)/((n:ℝ)+1)
  have ha (n : ℕ) : 0 < a n := by dsimp [a]; positivity
  have hax (n : ℕ) : 3*a n ≤ x := by
    have hn : 1 ≤ (n:ℝ)+1 := le_add_of_nonneg_left (Nat.cast_nonneg n)
    have hh : a n ≤ x/6 := div_le_self (by positivity) hn
    linarith
  let R (n : ℕ) : ℝ := ‖((x:ℂ),(0:ℝ))‖+(n:ℝ)+1
  have hR (n : ℕ) : 0 ≤ R n := by dsimp [R]; positivity
  have hR0 (n : ℕ) : ‖((x:ℂ),(0:ℝ))‖ ≤ R n := by dsimp [R]; have := Nat.cast_nonneg (α := ℝ) n; linarith
  let t (n : ℕ) : ℝ≥0 := ⟨(n:ℝ)+1,by positivity⟩
  let c (n : ℕ) := Classical.choice (exists_boundaryClockSolution B hm hBm hBc κ (a n) (ha n) (x:ℂ))
  let l (n : ℕ) : BoundaryLocalization (c n) α β (R n) H (t n) := Classical.choice
    (exists_boundaryLocalization hBc hB0 (c n) (ha n) α β (R n) H (t n) (hR0 n)
      (by simpa only [Complex.ofReal_re] using hax n) hH0)
  let E (n : ℕ) : Set Ω := {ω | H ≤ boundaryDensity κ α β ((c n).Q ((l n).τ ω) ω) (B ((l n).τ ω) ω)}
  have hprob (n : ℕ) : P (E n) ≤ ENNReal.ofReal (boundaryDensity κ α β (x:ℂ) 0/H) :=
    (l n).density_crossing_probability hB hBm hBc hκ (ha n) hβ (hR n) hH
  have hsub : {ω | ∃ (T : ℝ≥0) (Q : ℝ → ℂ),
      IsPositiveBoundaryClockPath (fun t => Real.sqrt κ*B t ω) x T Q ∧
      H ≤ boundaryDensity κ α β (Q T) (B T ω)} ⊆
      {ω | ∀ᶠ n : ℕ in atTop, ω ∈ E n} := by
    rintro ω ⟨S,Q,hQ,hhit⟩
    obtain ⟨g,hg,hgap⟩ := hQ.positive_lower_bound ((hBc ω).const_mul _)
    have hnc : ContinuousOn (fun u : ℝ => ‖(Q u,B u.toNNReal ω)‖) (Icc 0 (S:ℝ)) :=
      (hQ.continuousOn.prodMk (((hBc ω).comp continuous_real_toNNReal).continuousOn)).norm
    obtain ⟨s,hs,hmax⟩ := (isCompact_Icc : IsCompact (Icc 0 (S:ℝ))).exists_isMaxOn
      ⟨0,le_rfl,S.coe_nonneg⟩ hnc
    let M := ‖(Q s,B s.toNNReal ω)‖
    obtain ⟨N,hN⟩ := exists_nat_gt (max (max (S:ℝ) M) (x/(2*g)))
    filter_upwards [eventually_ge_atTop N] with n hn
    have hn' : (N:ℝ) ≤ n := Nat.cast_le.mpr hn
    have hNS : (S:ℝ) < (n:ℝ)+1 := by have := (le_max_left (S:ℝ) M).trans (le_max_left (max (S:ℝ) M) (x/(2*g))); linarith
    have hNM : M < (n:ℝ)+1 := by have := (le_max_right (S:ℝ) M).trans (le_max_left (max (S:ℝ) M) (x/(2*g))); linarith
    have hNg : x/(2*g) < (n:ℝ)+1 := by have := le_max_right (max (S:ℝ) M) (x/(2*g)); linarith
    have hann : 3*a n < g := by
      have hn0 : 0 < (n:ℝ)+1 := by positivity
      have hh : x < ((n:ℝ)+1)*(2*g) := (div_lt_iff₀ (by positivity)).mp hNg
      rw [show 3*a n = (x/2)/((n:ℝ)+1) by dsimp only [a]; ring]
      apply (div_lt_iff₀ hn0).mpr
      nlinarith
    apply (l n).true_crossing_forces_density_boundary (ha n) ω S
      (NNReal.coe_lt_coe.mp hNS) Q hQ
    · intro u hu
      exact hann.trans_le (hgap u hu)
    · intro u hu
      have hm := hmax ⟨u.coe_nonneg,NNReal.coe_le_coe.mpr hu⟩
      change ‖(Q (u:ℝ),B (u:ℝ).toNNReal ω)‖ ≤ M at hm
      rw [Real.toNNReal_coe] at hm
      have hnorm : 0 ≤ ‖((x:ℂ),(0:ℝ))‖ := norm_nonneg _
      change ‖(Q (u:ℝ),B u ω)‖ < ‖((x:ℂ),(0:ℝ))‖+(n:ℝ)+1
      change ‖(Q (u:ℝ),B u ω)‖ ≤ M at hm
      linarith
    · exact hhit
  exact (measure_mono hsub).trans (measure_eventually_sets_le P E _ hprob)

 

theorem boundary_maximal_density
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (κ α β x H : ℝ) (hκ : 0 < κ) (hx : 0 < x) (hH : 0 < H)
    (hβ : -α-2+κ*(β+1)/2=0)
    (hH0 : boundaryDensity κ α β (x:ℂ) 0 ≤ H) :
    P {ω | ∃ (T : ℝ≥0) (Q : ℝ → ℂ),
      IsPositiveBoundaryClockPath (fun t => Real.sqrt κ*B t ω) x T Q ∧
      H ≤ boundaryDensity κ α β (Q T) (B T ω)} ≤
      ENNReal.ofReal (boundaryDensity κ α β (x:ℂ) 0 / H) := by
  obtain ⟨C,hCm,hCc,hC0,hC,hCB⟩ := exists_regular_brownian_version hB
  apply (measure_mono_ae (show {ω | ∃ (T : ℝ≥0) (Q : ℝ → ℂ),
      IsPositiveBoundaryClockPath (fun t => Real.sqrt κ*B t ω) x T Q ∧
      H ≤ boundaryDensity κ α β (Q T) (B T ω)} ≤ᵐ[P]
      {ω | ∃ (T : ℝ≥0) (Q : ℝ → ℂ),
      IsPositiveBoundaryClockPath (fun t => Real.sqrt κ*C t ω) x T Q ∧
      H ≤ boundaryDensity κ α β (Q T) (C T ω)} from ?_)).trans
      (boundary_maximal_density_regular hC hCm hCc hC0 κ α β x H hκ hx hH hβ hH0)
  filter_upwards [hCB] with ω he
  rintro ⟨T,Q,hQ,hF⟩
  refine ⟨T,Q,?_,?_⟩
  · simpa only [he] using hQ
  · simpa only [he] using hF

end SLEExactGauge
end

 
section

open Set Filter MeasureTheory Complex
open scoped Topology NNReal
namespace SLEExactGauge

 

theorem IsCapacityTwoWitness.forward_flow_survives
    {U : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}
    (h : IsCapacityTwoWitness U γ G F) (T : ℝ≥0) (Q : ℝ → ℂ)
    (hpos : ∀ t ∈ Icc 0 (T:ℝ), 0 < (Q t).im)
    (hd : ∀ t ∈ Icc 0 (T:ℝ), HasDerivWithinAt Q
      (2 / (Q t - (U t.toNNReal : ℂ))) (Icc 0 (T:ℝ)) t) :
    Q 0 ∈ survivingDomain γ T ∧ G T (Q 0) = Q T := by
  have hc : ContinuousOn (fun t => (Q t).im) (Icc 0 (T:ℝ)) :=
    Complex.continuous_im.comp_continuousOn (fun t ht => (hd t ht).continuousWithinAt)
  obtain ⟨t₀,ht₀,hmin⟩ := (isCompact_Icc : IsCompact (Icc 0 (T:ℝ))).exists_isMinOn
    ⟨0,le_rfl,T.coe_nonneg⟩ hc
  let a := (Q t₀).im
  have ha : 0 < a := hpos t₀ ht₀
  have hbound (t : ℝ) (ht : t ∈ Icc 0 (T:ℝ)) : a ≤ (Q t).im := hmin ht
  have hmap : MapsTo (fun t : ℝ => (T:ℝ)-t) (Icc 0 (T:ℝ)) (Icc 0 (T:ℝ)) := by
    intro t ht; constructor <;> linarith [ht.1,ht.2]
  have hrev (t : ℝ) (ht : t ∈ Icc 0 (T:ℝ)) :
      HasDerivWithinAt (fun s : ℝ => Q ((T:ℝ)-s))
        (reverseField a (U ((T:ℝ)-t).toNNReal) (Q ((T:ℝ)-t))) (Icc 0 (T:ℝ)) t := by
    have he := (hd _ (hmap ht)).scomp t
      ((hasDerivAt_id t).const_sub (T:ℝ)).hasDerivWithinAt hmap
    simpa only [Function.comp_def,neg_smul,one_smul,reverseField,
      reverseCenter_eq (hbound _ (hmap ht)),div_eq_mul_inv,neg_mul] using he
  have he := h.reverse_flow_identifies T (Q T) ha
    (hbound T ⟨T.coe_nonneg,le_rfl⟩) (fun s => Q ((T:ℝ)-s))
    (by simp only [sub_zero]) hrev
  simp only [sub_self] at he
  have hlive : F T (Q T) ∈ survivingDomain γ T :=
    h.2.2.2.2.2.2.1 T (hpos T ⟨T.coe_nonneg,le_rfl⟩)
  rw [← he] at hlive
  refine ⟨hlive,?_⟩
  rw [he]
  exact h.2.2.2.2.2.2.2.2.1 T (Q T) (hpos T ⟨T.coe_nonneg,le_rfl⟩)

end SLEExactGauge
end

 
end

end OAI
